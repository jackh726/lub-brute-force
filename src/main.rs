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

#[derive(Copy, Clone, Debug)]
enum FindLubVersion {
    Main,
    NoMutualCoercion,
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
    version: FindLubVersion,
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
        let unsize_found = unsize.neighbors(node).iter().any(|u| *u == lub);
        tracing::debug!("Unsize found from node to LUB: {unsize_found}");
        let deref_found = 'deref_found: {
            let mut current_node = node;
            let mut deref_adjs = Vec::with_capacity(nodes.len());
            while let Some(deref_target) = deref.neighbors(current_node).first() {
                current_node = *deref_target;
                deref_adjs.push((current_node, EdgeType::Deref));
                if current_node == lub {
                    break 'deref_found Some(deref_adjs);
                }
                if current_node == node {
                    unreachable!(
                        "Deref cycle found - though should be unreachable by construction."
                    );
                }
            }
            None
        };
        tracing::debug!("Deref chain from node to LUB: {deref_found:?}");
        if let FindLubVersion::NoMutualCoercion = version
            && unsize_found
            && let Some(_) = &deref_found
        {
            tracing::debug!("mutual coercion found -> bailing");
            return None;
        }
        if unsize_found {
            adjustments_by_node[node].path.push((lub, EdgeType::Unsize));
            continue;
        }
        if let Some(deref_found) = deref_found {
            adjustments_by_node[node].path.extend(deref_found);
            continue;
        }

        // Then check if there exists a coercion from the current LUB to the new node
        let unsize_found = unsize.neighbors(lub).iter().any(|u| *u == node);
        tracing::debug!("Unsize found from LUB to to node: {unsize_found}");
        let deref_found = 'deref_found: {
            let mut current_node = lub;
            let mut deref_adjs = Vec::with_capacity(nodes.len());
            while let Some(deref_target) = deref.neighbors(current_node).first() {
                current_node = *deref_target;
                deref_adjs.push((current_node, EdgeType::Deref));
                if current_node == node {
                    break 'deref_found Some(deref_adjs);
                }
                if current_node == lub {
                    unreachable!(
                        "Deref cycle found - though should be unreachable by construction."
                    );
                }
            }
            None
        };
        tracing::debug!("Deref chain found from LUB to to node: {deref_found:?}");
        if let FindLubVersion::NoMutualCoercion = version
            && unsize_found
            && let Some(_) = &deref_found
        {
            tracing::debug!("mutual coercion found -> bailing");
            return None;
        }
        if unsize_found {
            for j in nodes[0..i].iter().copied() {
                adjustments_by_node[j].path.push((node, EdgeType::Unsize));
            }
            lub = node;
            continue;
        }
        if let Some(deref_found) = deref_found {
            for j in nodes[0..i].iter().copied() {
                adjustments_by_node[j]
                    .path
                    .extend(deref_found.iter().copied());
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
    version: FindLubVersion,
) -> anyhow::Result<Option<(usize, Vec<Adjustment>)>> {
    use itertools::Itertools;

    let orderings: Vec<Vec<_>> = (0..n).permutations(n).collect();

    let first = find_lub(&orderings[0], deref, unsize, version);
    writeln!(file, "d{di}-u{ui}")?;
    writeln!(file, "  {:?}: {first:?}", orderings[0])?;

    for order in orderings.iter().skip(1) {
        let new_lub = find_lub(&order, deref, unsize, version);
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

fn main() -> anyhow::Result<()> {
    tracing_subscriber::registry()
        .with(tracing_tree::HierarchicalLayer::new(2))
        .with(tracing_subscriber::EnvFilter::from_default_env())
        .init();

    for n in 3..=5 {
        let file = File::create(&format!("target/{n}-lubs.txt"))?;
        let mut file = BufWriter::new(file);
        println!("Testing with {} nodes", n);

        let deref_graphs = generate_deref_graphs(n);
        let unsize_graphs = generate_unsizing_graphs(n);

        println!("  Deref graphs: {}", deref_graphs.len());
        println!("  Unsize graphs: {}", unsize_graphs.len());
        println!(
            "  Total pairs: {}",
            deref_graphs.len() * unsize_graphs.len()
        );

        write_graphs(&format!("target/{n}-deref.txt"), &deref_graphs)?;
        write_graphs(&format!("target/{n}-unsize.txt"), &unsize_graphs)?;

        let mut any_errors = false;
        let total = deref_graphs.len() * unsize_graphs.len();
        let mut count = 0;
        for (di, deref) in deref_graphs.iter().enumerate() {
            for (ui, unsize) in unsize_graphs.iter().enumerate() {
                count += 1;
                if count % 10000 == 0 {
                    println!("  Progress: {}/{}", count, total);
                }

                let res_main =
                    do_find_inner(&mut file, n, di, deref, ui, unsize, FindLubVersion::Main);
                let res_no_mut = do_find_inner(
                    &mut file,
                    n,
                    di,
                    deref,
                    ui,
                    unsize,
                    FindLubVersion::NoMutualCoercion,
                );
                match (&res_main, &res_no_mut) {
                    (Ok(_), Ok(_)) => {}
                    (Err(_), Err(_)) => {}
                    _ => {
                        //tracing::info!(?res_main, ?res_no_mut, "change in behavior");
                    }
                }
                match &res_no_mut {
                    Ok(_) => {}
                    Err(e) => {
                        any_errors = true;
                        tracing::info!(?e, "error in NoMututalCoercion");
                    }
                }
            }
        }
        if any_errors {
            break;
            carg
        }
    }
    Ok(())
}
