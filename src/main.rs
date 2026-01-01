//! Fuzzer for testing LUB (Least Upper Bound) coercion algorithms.
//!
//! This fuzzer generates all possible digraphs for deref and unsizing coercions,
//! then tests whether different orderings of match arms produce consistent results.

use lub_fuzz::*;
use std::{
    collections::HashMap,
    fmt::{Debug, Write as _},
    fs::File,
    io::{BufWriter, Write},
};
use tracing_subscriber::prelude::*;

/// Represents an adjustment path from a node to the LUB type.
type Adjustment = Vec<(NodeId, EdgeType)>;

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
    let mut adjustments_by_node = vec![vec![]; max_node + 1];
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

        adjustments_by_node[start_node] = reachable.get(&lub).cloned().unwrap_or_default();
    }

    Some((common_lub?, adjustments_by_node))
}

fn does_unsize(from: NodeId, to: NodeId, unsize: &Graph) -> Option<Vec<(usize, EdgeType)>> {
    unsize
        .neighbors(from)
        .iter()
        .any(|u| *u == to)
        .then(|| vec![(to, EdgeType::Unsize)])
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

fn does_coerce(
    from: NodeId,
    to: NodeId,
    unsize: &Graph,
    deref: &Graph,
) -> Option<Vec<(usize, EdgeType)>> {
    does_unsize(from, to, unsize).or_else(|| does_deref(from, to, deref))
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
    let mut adjustments_by_node = vec![vec![]; nodes.len()];

    for (i, node) in nodes.iter().copied().enumerate() {
        let arm_span = tracing::debug_span!("arm coercion", ?node, ?lub, ?adjustments_by_node);
        let _span = arm_span.enter();

        if node == lub {
            // Node is equal to the LUB (in this algorithm, will only actually happen on the first branch)
            // Nothing to do, no adjustments to be made
            continue;
        }

        // First check if there exists a coercion to the LUB
        let coerce_to_lub = does_coerce(node, lub, unsize, deref);
        // Then check if there exists a coercion from the current LUB to the new node
        let coerce_to_new = does_coerce(lub, node, unsize, deref);

        tracing::debug!(?coerce_to_lub, ?coerce_to_new);

        if coerce_to_lub.is_some()
            && coerce_to_new.is_some()
            && changes.contains(&AlgoChanges::NoMutualCoercion)
        {
            tracing::debug!("mutual coercion found -> bailing");
            return None;
        }

        if let Some(coerce) = coerce_to_lub {
            adjustments_by_node[node].extend(coerce);
            continue;
        }

        if !changes.contains(&AlgoChanges::RequireDirect) {
            if let Some(coerce) = coerce_to_new {
                for j in nodes[0..i].iter().copied() {
                    adjustments_by_node[j].extend(coerce.iter().copied());
                }
                lub = node;
                continue;
            }
        } else {
            if let Some(_) = coerce_to_new {
                for j in nodes[0..i].iter().copied() {
                    let coerce_direct = does_coerce(j, node, unsize, deref);
                    if let Some(coerce_direct) = coerce_direct {
                        adjustments_by_node[j] = coerce_direct;
                    } else {
                        tracing::debug!(?j, ?node, "no direct coercion available");
                        return None;
                    }
                }
                lub = node;
                continue;
            }
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

#[allow(dead_code)]
fn error_string(error: &Error, di: usize, deref: &Graph, ui: usize, unsize: &Graph) -> String {
    let mut mismatch_string = "\n".to_string();
    writeln!(mismatch_string, "!!! MISMATCH FOUND ({:?}) !!!", error.kind).unwrap();
    writeln!(
        mismatch_string,
        "Deref graph #{}: {:?}",
        di,
        deref.to_adj_list()
    )
    .unwrap();
    writeln!(
        mismatch_string,
        "Unsize graph #{}: {:?}",
        ui,
        unsize.to_adj_list()
    )
    .unwrap();
    let Error {
        first_order,
        second_order,
        first_result,
        second_result,
        ..
    } = error;
    writeln!(mismatch_string, "  {first_order:?}: {first_result:?}").unwrap();
    writeln!(mismatch_string, "  {second_order:?}: {second_result:?}").unwrap();

    mismatch_string
}

fn print_map<K: Debug, V: Debug>(map: &HashMap<K, V>) -> String {
    let mut ret = String::new();
    for (k, v) in map.iter() {
        ret.push_str(&format!("  {k:?}: {v:?}\n"));
    }
    ret
}

#[derive(Clone, Debug)]
struct Error {
    kind: ErrorKind,
    first_order: Vec<NodeId>,
    second_order: Vec<NodeId>,
    first_result: Option<(usize, Vec<Adjustment>)>,
    second_result: Option<(usize, Vec<Adjustment>)>,
}
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum ErrorKind {
    DifferentLUB,
    DifferentAdjustments(NodeId),
}

fn do_find_inner(
    mut file: Option<&mut BufWriter<File>>,
    di: usize,
    deref: &Graph,
    ui: usize,
    unsize: &Graph,
    changes: &[AlgoChanges],
) -> Result<Option<(usize, Vec<Adjustment>)>, Box<Error>> {
    use itertools::Itertools;

    let orderings: Vec<Vec<_>> = (0..deref.len()).permutations(deref.len()).collect();

    let first = find_lub(&orderings[0], deref, unsize, changes);
    if let Some(file) = file.as_mut() {
        writeln!(file, "d{di}-u{ui}").unwrap();
        writeln!(file, "  {:?}: {first:?}", orderings[0]).unwrap();
    }

    for order in orderings.iter().skip(1) {
        let new_lub = find_lub(&order, deref, unsize, changes);
        if let Some(file) = file.as_mut() {
            writeln!(file, "  {order:?}: {new_lub:?}").unwrap();
        }
        if first != new_lub {
            let kind = match (&first, &new_lub) {
                (Some(first), Some(second)) if first.0 != second.0 => ErrorKind::DifferentLUB,

                (None, Some(_)) | (Some(_), None) => ErrorKind::DifferentLUB,
                (Some(first), Some(_)) => ErrorKind::DifferentAdjustments(first.0),
                (None, None) => unreachable!(),
            };
            return Err(Box::new(Error {
                kind,
                first_order: orderings[0].clone(),
                second_order: order.clone(),
                first_result: first,
                second_result: new_lub,
            }));
        }
    }

    Ok(first)
}

#[derive(Default, Debug)]
struct Stats {
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
        let mut paired_stats: HashMap<_, usize> = HashMap::new();
        for (di, deref) in deref_graphs.iter().enumerate() {
            for (ui, unsize) in unsize_graphs.iter().enumerate() {
                count += 1;
                if count % 10000 == 0 {
                    println!("  Progress: {}/{}", count, total);
                }

                let res_main = do_find_inner(Some(&mut file), di, deref, ui, unsize, &[]);
                let res_no_mut = do_find_inner(
                    Some(&mut file),
                    di,
                    deref,
                    ui,
                    unsize,
                    &[AlgoChanges::NoMutualCoercion, AlgoChanges::RequireDirect],
                );
                match (&res_main, &res_no_mut) {
                    (Ok(Some(v)), Ok(None)) => {
                        *paired_stats.entry((Ok(Some(v.0)), Ok(None))).or_default() += 1;
                        //tracing::info!(?res_main, ?res_no_mut, "change in behavior");
                    }
                    (Ok(None), Ok(Some(v))) => {
                        *paired_stats.entry((Ok(None), Ok(Some(v.0)))).or_default() += 1;
                    }
                    (Ok(Some(v1)), Ok(Some(v2))) => {
                        *paired_stats
                            .entry((Ok(Some(v1.0)), Ok(Some(v2.0))))
                            .or_default() += 1;
                    }
                    (Ok(None), Ok(None)) => {
                        *paired_stats.entry((Ok(None), Ok(None))).or_default() += 1;
                    }
                    (Err(e1), Err(e2)) => {
                        *paired_stats
                            .entry((Err(e1.kind), Err(e2.kind)))
                            .or_default() += 1;
                    }
                    (Ok(Some(v)), Err(e)) => {
                        *paired_stats
                            .entry((Ok(Some(v.0)), Err(e.kind)))
                            .or_default() += 1;
                        //tracing::info!(?res_main, change_error = error_string(&**e, di, deref, ui, unsize), "change in behavior");
                    }
                    (Ok(None), Err(e)) => {
                        *paired_stats.entry((Ok(None), Err(e.kind))).or_default() += 1;
                        //tracing::info!(?res_main, change_error = error_string(&**e, di, deref, ui, unsize), "change in behavior");
                    }
                    (Err(e), Ok(None)) => {
                        *paired_stats.entry((Err(e.kind), Ok(None))).or_default() += 1;
                        //tracing::info!(main_error = error_string(&**e, di, deref, ui, unsize), ?res_no_mut, "change in behavior");
                    }
                    (Err(e), Ok(Some(v))) => {
                        *paired_stats
                            .entry((Err(e.kind), Ok(Some(v.0))))
                            .or_default() += 1;
                        //tracing::info!(main_error = display(error_string(&**e, di, deref, ui, unsize)), ?res_no_mut, "change in behavior");
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
        println!("Algorithm comparison stats:\n{}", print_map(&paired_stats));
    }
    Ok(())
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn ex5() {
        let deref = &Graph::from_adj_list(vec![vec![1], vec![3], vec![3], vec![]]);
        let unsize = &Graph::from_adj_list(vec![vec![], vec![], vec![], vec![]]);

        let order_a = &[0, 1, 2, 3];
        let order_b = &[3, 0, 1, 2];

        let main_a = find_lub(order_a, deref, unsize, &[]);
        let mod_a = find_lub(
            order_a,
            deref,
            unsize,
            &[AlgoChanges::NoMutualCoercion, AlgoChanges::RequireDirect],
        );
        let main_b = find_lub(order_b, deref, unsize, &[]);
        let mod_b = find_lub(
            order_b,
            deref,
            unsize,
            &[AlgoChanges::NoMutualCoercion, AlgoChanges::RequireDirect],
        );
        assert_eq!(main_a, None);
        assert_eq!(mod_a, None);
        assert_eq!(
            main_b,
            Some((
                3,
                vec![
                    vec![(1, EdgeType::Deref), (3, EdgeType::Deref)],
                    vec![(3, EdgeType::Deref)],
                    vec![(3, EdgeType::Deref)],
                    vec![]
                ]
            ))
        );
        assert_eq!(
            mod_b,
            Some((
                3,
                vec![
                    vec![(1, EdgeType::Deref), (3, EdgeType::Deref)],
                    vec![(3, EdgeType::Deref)],
                    vec![(3, EdgeType::Deref)],
                    vec![]
                ]
            ))
        );
    }
}
