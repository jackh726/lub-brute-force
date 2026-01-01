//! Fuzzer for testing LUB (Least Upper Bound) coercion algorithms.
//!
//! This fuzzer generates all possible digraphs for deref and unsizing coercions,
//! then tests whether different orderings of match arms produce consistent results.

use lub_fuzz::*;
use std::{
    collections::HashMap,
    fmt::Write as _,
    fs::File,
    io::{BufWriter, Write},
};
use tracing_subscriber::prelude::*;

/// Represents an adjustment path from a node to the LUB type.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Adjustment {
    path: Vec<(NodeId, EdgeType)>,
}

/// Type of coercion edge in the graph.
#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum EdgeType {
    Deref,
    Unsize,
}

/// Finds the LUB type and adjustment paths for each node.
///
/// Returns `Some((lub, adjustments))` if a common LUB exists for all nodes,
/// where `adjustments[node_id]` is the path from that node to the LUB.
/// Each step in the path is (next_node, edge_type) to reach that node.
/// Returns `None` if no common LUB can be found.
// This is just a function to verify that the rest of the fuzzing code works.
#[allow(dead_code)]
fn find_lub_simple(
    nodes: &[NodeId],
    deref: &Graph,
    unsize: &Graph,
) -> Option<(NodeId, Vec<Adjustment>)> {
    let max_node = *nodes.iter().max()?;
    let mut adjustments_by_node = vec![Adjustment { path: vec![] }; max_node + 1];
    let mut common_lub = None;

    for &start_node in nodes {
        let mut reachable = HashMap::new();
        let mut queue = vec![(start_node, vec![])];

        while let Some((current, path)) = queue.pop() {
            if reachable.contains_key(&current) {
                continue;
            }
            reachable.insert(current, path.clone());

            for &next in deref.neighbors(current) {
                let mut new_path = path.clone();
                new_path.push((next, EdgeType::Deref));
                queue.push((next, new_path));
            }
            for &next in unsize.neighbors(current) {
                let mut new_path = path.clone();
                new_path.push((next, EdgeType::Unsize));
                queue.push((next, new_path));
            }
        }

        let lub = *reachable.keys().max()?;

        if let Some(expected_lub) = common_lub {
            if lub != expected_lub {
                return None;
            }
        } else {
            common_lub = Some(lub);
        }

        let path = reachable.get(&lub).cloned().unwrap_or_default();
        adjustments_by_node[start_node] = Adjustment { path };
    }

    Some((common_lub?, adjustments_by_node))
}

fn does_unsize(from: NodeId, to: NodeId, unsize: &Graph) -> bool {
    unsize.neighbors(from).iter().any(|u| *u == to)
}

fn does_deref(from: NodeId, to: NodeId, deref: &Graph) -> Option<Vec<(usize, EdgeType)>> {
    let mut current_node = from;
    let mut deref_adjs = Vec::with_capacity(deref.len());
    while let Some(deref_target) = deref.neighbors(current_node).first() {
        current_node = *deref_target;
        deref_adjs.push((current_node, EdgeType::Deref));
        if current_node == to {
            return Some(deref_adjs);
        }
        if current_node == from {
            unreachable!("Deref cycle found - though should be unreachable by construction.");
        }
    }
    None
}

#[derive(Copy, Clone, Debug, PartialEq)]
enum AlgoChanges {
    NoMutualCoercion,
    RequireDirect,
}

/// Finds the LUB type and adjustment paths for each node.
///
/// Returns `Some((lub, adjustments))` if a common LUB exists for all nodes,
/// where `adjustments[node_id]` is the path from that node to the LUB.
/// Each step in the path is (next_node, edge_type) to reach that node.
/// Returns `None` if no common LUB can be found.
#[tracing::instrument(level = "debug", skip(deref, unsize), ret)]
fn find_lub(
    nodes: &[NodeId],
    deref: &Graph,
    unsize: &Graph,
    changes: &[AlgoChanges],
) -> Option<(NodeId, Vec<Adjustment>)> {
    tracing::debug!(deref = ?deref.to_adj_list(), unsize = ?unsize.to_adj_list());
    let mut lub = nodes[0];
    let mut adjustments_by_node = vec![Adjustment { path: vec![] }; nodes.len()];

    for (i, node) in nodes.iter().copied().enumerate() {
        let arm_span = tracing::debug_span!("arm coercion", ?node, ?lub, ?adjustments_by_node);
        let _span = arm_span.enter();

        if node == lub {
            // Node is equal to the LUB (in this algorithm, will only actually happen on the first branch)
            // Nothing to do, no adjustments to be made
            continue;
        }

        // First check if there exists a coercion to the LUB
        let unsize_to_lub = does_unsize(node, lub, unsize);
        tracing::debug!("Unsize found from node to LUB: {unsize_to_lub}");
        let deref_to_lub = does_deref(node, lub, deref);
        tracing::debug!("Deref chain from node to LUB: {deref_to_lub:?}");

        // Then check if there exists a coercion from the current LUB to the new node
        let unsize_to_new = does_unsize(lub, node, unsize);
        tracing::debug!("Unsize found from LUB to new node: {unsize_to_new}");
        let deref_to_new = does_deref(lub, node, deref);
        tracing::debug!("Deref chain found from LUB to new node: {deref_to_new:?}");

        if (unsize_to_lub || deref_to_lub.is_some())
            && (unsize_to_new || deref_to_new.is_some())
            && changes.contains(&AlgoChanges::NoMutualCoercion)
        {
            tracing::debug!("mutual coercion found -> bailing");
            return None;
        }

        if unsize_to_lub {
            adjustments_by_node[node].path.push((lub, EdgeType::Unsize));
            continue;
        }
        if let Some(deref_found) = deref_to_lub {
            adjustments_by_node[node].path.extend(deref_found);
            continue;
        }

        if unsize_to_new {
            for j in nodes[0..i].iter().copied() {
                adjustments_by_node[j].path.push((node, EdgeType::Unsize));
            }
            if !changes.contains(&AlgoChanges::RequireDirect) {
                for j in nodes[0..i].iter().copied() {
                    adjustments_by_node[j].path.push((node, EdgeType::Unsize));
                }
            } else {
                for j in nodes[0..i].iter().copied() {
                    let unsize_direct = does_unsize(j, node, unsize);
                    let deref_direct = does_deref(j, node, deref);
                    if unsize_direct {
                        adjustments_by_node[j].path = vec![(node, EdgeType::Unsize)];
                    } else if let Some(deref_direct) = deref_direct {
                        adjustments_by_node[j].path = deref_direct;
                    } else {
                        tracing::debug!(?j, ?node, "no direct coercion available");
                        return None;
                    }
                }
            }
            lub = node;
            continue;
        }
        if let Some(deref_found) = deref_to_new {
            if !changes.contains(&AlgoChanges::RequireDirect) {
                for j in nodes[0..i].iter().copied() {
                    adjustments_by_node[j]
                        .path
                        .extend(deref_found.iter().copied());
                }
            } else {
                for j in nodes[0..i].iter().copied() {
                    let unsize_direct = does_unsize(j, node, unsize);
                    let deref_direct = does_deref(j, node, deref);
                    if unsize_direct {
                        adjustments_by_node[j].path = vec![(node, EdgeType::Unsize)];
                    } else if let Some(deref_direct) = deref_direct {
                        adjustments_by_node[j].path = deref_direct;
                    } else {
                        tracing::debug!(?j, ?node, "no direct coercion available");
                        return None;
                    }
                }
            }
            lub = node;
            continue;
        }

        return None;
    }

    Some((lub, adjustments_by_node))
}

/// Writes graphs to a file for inspection.
fn write_graphs(file: &str, graphs: &[Graph]) -> anyhow::Result<()> {
    let file = File::create(file)?;
    let mut file = BufWriter::new(file);
    for (i, graph) in graphs.iter().enumerate() {
        writeln!(file, "{i}: {:?}", graph.to_adj_list())?;
    }
    Ok(())
}

fn do_find_inner(
    file: &mut BufWriter<File>,
    n: usize,
    di: usize,
    deref: &Graph,
    ui: usize,
    unsize: &Graph,
    changes: &[AlgoChanges],
) -> anyhow::Result<Option<(usize, Vec<Adjustment>)>> {
    use itertools::Itertools;

    let orderings: Vec<Vec<_>> = (0..n).permutations(n).collect();

    let first = find_lub(&orderings[0], deref, unsize, changes);
    writeln!(file, "d{di}-u{ui}")?;
    writeln!(file, "  {:?}: {first:?}", orderings[0])?;

    for order in orderings.iter().skip(1) {
        let new_lub = find_lub(&order, deref, unsize, changes);
        writeln!(file, "  {order:?}: {new_lub:?}")?;
        if new_lub != first {
            let mut mismatch_string = "\n".to_string();
            writeln!(mismatch_string, "!!! MISMATCH FOUND !!!")?;
            writeln!(
                mismatch_string,
                "Deref graph #{}: {:?}",
                di,
                deref.to_adj_list()
            )?;
            writeln!(
                mismatch_string,
                "Unsize graph #{}: {:?}",
                ui,
                unsize.to_adj_list()
            )?;
            writeln!(mismatch_string, "  {:?}: {first:?}", &orderings[0])?;
            writeln!(mismatch_string, "  {:?}: {new_lub:?}", &order)?;
            anyhow::bail!(mismatch_string);
        }
    }

    Ok(first)
}

#[derive(Default, Debug)]
struct Stats {
    ok_some_to_ok_none: usize,
    both_ok: usize,
    both_err: usize,
    main_ok_no_mut_err: usize,
    main_err_no_mut_ok_none: usize,
    main_err_no_mut_ok_some: usize,
    no_mut_ok: usize,
    no_mut_err: usize,
}

fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(tracing_tree::HierarchicalLayer::new(2))
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    for n in 3..=4 {
        let file = File::create(&format!("target/{n}-lubs.txt"))?;
        let mut file = BufWriter::new(file);
        println!("Testing with {} nodes", n);

        let deref_graphs = generate_deref_graphs(n, false);
        let unsize_graphs = generate_unsizing_graphs(n, false);

        println!("  Deref graphs: {}", deref_graphs.len());
        println!("  Unsize graphs: {}", unsize_graphs.len());
        println!(
            "  Total pairs: {}",
            deref_graphs.len() * unsize_graphs.len()
        );

        write_graphs(&format!("target/{n}-deref.txt"), &deref_graphs)?;
        write_graphs(&format!("target/{n}-unsize.txt"), &unsize_graphs)?;

        let total = deref_graphs.len() * unsize_graphs.len();
        let mut count = 0;
        let mut stats = Stats::default();
        for (di, deref) in deref_graphs.iter().enumerate() {
            for (ui, unsize) in unsize_graphs.iter().enumerate() {
                count += 1;
                if count % 10000 == 0 {
                    println!("  Progress: {}/{}", count, total);
                }

                let res_main = do_find_inner(&mut file, n, di, deref, ui, unsize, &[]);
                let res_no_mut = do_find_inner(
                    &mut file,
                    n,
                    di,
                    deref,
                    ui,
                    unsize,
                    &[AlgoChanges::NoMutualCoercion, AlgoChanges::RequireDirect],
                );
                match (&res_main, &res_no_mut) {
                    (Ok(Some(_)), Ok(None)) => {
                        stats.ok_some_to_ok_none += 1;
                        //tracing::info!(?res_main, ?res_no_mut, "change in behavior");
                    }
                    (Ok(_), Ok(_)) => stats.both_ok += 1,
                    (Err(_), Err(_)) => stats.both_err += 1,
                    (Ok(_), Err(_)) => {
                        stats.main_ok_no_mut_err += 1;
                        //tracing::info!(?res_main, ?res_no_mut, "change in behavior");
                    }
                    (Err(_), Ok(None)) => {
                        stats.main_err_no_mut_ok_none += 1;
                        //tracing::info!(?res_main, ?res_no_mut, "change in behavior");
                    }
                    (Err(_), Ok(Some(_))) => {
                        stats.main_err_no_mut_ok_some += 1;
                        tracing::info!(?res_main, ?res_no_mut, "change in behavior");
                    }
                }
                match &res_no_mut {
                    Ok(_) => {
                        stats.no_mut_ok += 1;
                    }
                    Err(_) => {
                        stats.no_mut_err += 1;
                        //tracing::info!(?res_no_mut, "error in NoMututalCoercion");
                    }
                }
            }
        }
        println!("Algorithm comparison stats: {:#?}", stats);
    }
    Ok(())
}
