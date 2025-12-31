//! Fuzzer for testing LUB (Least Upper Bound) coercion algorithms.
//!
//! This fuzzer generates all possible digraphs for deref and unsizing coercions,
//! then tests whether different orderings of match arms produce consistent results.

use lub_fuzz::*;
use std::{
    collections::HashMap,
    fs::File,
    io::{BufWriter, Write},
};

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
fn find_lub(nodes: &[NodeId], deref: &Graph, unsize: &Graph) -> Option<(NodeId, Vec<Adjustment>)> {
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

/// Writes graphs to a file for inspection.
fn write_graphs(file: &str, graphs: &[Graph]) -> anyhow::Result<()> {
    let file = File::create(file)?;
    let mut file = BufWriter::new(file);
    for (i, graph) in graphs.iter().enumerate() {
        writeln!(file, "{i}: {:?}", graph.to_adj_list())?;
    }
    Ok(())
}

fn main() -> anyhow::Result<()> {
    use itertools::Itertools;

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

        let total = deref_graphs.len() * unsize_graphs.len();
        let mut count = 0;
        for (di, deref) in deref_graphs.iter().enumerate() {
            for (ui, unsize) in unsize_graphs.iter().enumerate() {
                count += 1;
                if count % 10000 == 0 {
                    println!("  Progress: {}/{}", count, total);
                }

                let orderings: Vec<Vec<_>> = (0..n).permutations(n).collect();
                let first = find_lub(&orderings[0], deref, unsize);
                writeln!(file, "{di}-{ui}")?;

                for order in orderings.iter() {
                    let new_lub = find_lub(&order, deref, unsize);
                    writeln!(file, "  {order:?}: {new_lub:?}")?;
                    if new_lub != first {
                        println!("\n!!! MISMATCH FOUND !!!");
                        println!("Deref graph #{}: {:?}", di, deref);
                        println!("Unsize graph #{}: {:?}", ui, unsize);
                        println!("  {:?}: {first:?}", &orderings[0]);
                        println!("  {:?}: {new_lub:?}", &order);
                        return Err(anyhow::anyhow!("Mismatch found"));
                    }
                }
            }
        }
    }
    Ok(())
}
