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
/// where `adjustments[i]` is the path from node `i` to the LUB.
/// Returns `None` if no common LUB can be found.
fn find_lub(nodes: &[NodeId], deref: &Graph, unsize: &Graph) -> Option<(NodeId, Vec<Adjustment>)> {
    let mut all_adjustments = Vec::with_capacity(nodes.len());
    let mut common_lub = None;

    for &node in nodes {
        let mut reachable = HashMap::new();
        let mut queue = vec![(node, vec![])];

        while let Some((current, path)) = queue.pop() {
            if reachable.contains_key(&current) {
                continue;
            }
            reachable.insert(current, path.clone());

            for &next in deref.neighbors(current) {
                let mut new_path = path.clone();
                new_path.push((current, EdgeType::Deref));
                queue.push((next, new_path));
            }
            for &next in unsize.neighbors(current) {
                let mut new_path = path.clone();
                new_path.push((current, EdgeType::Unsize));
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
        all_adjustments.push(Adjustment { path });
    }

    Some((common_lub?, all_adjustments))
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
                writeln!(file, "{di}-{ui}: {first:?}")?;

                let mismatch = orderings[1..]
                    .iter()
                    .any(|ordering| find_lub(ordering, deref, unsize) != first);

                if mismatch {
                    println!("\n!!! MISMATCH FOUND !!!");
                    println!("Deref graph #{}: {:?}", di, deref.to_adj_list());
                    println!("Unsize graph #{}: {:?}", ui, unsize.to_adj_list());
                    let results: Vec<_> = orderings
                        .iter()
                        .map(|ordering| (ordering, find_lub(ordering, deref, unsize)))
                        .collect();
                    for (ordering, result) in results {
                        println!("  Ordering: {:?}", ordering);
                        println!("  Result: {:?}", result);
                        writeln!(file, "  {ordering:?}: {result:?}")?;
                    }
                    return Err(anyhow::anyhow!("Mismatch found"));
                }
            }
        }
    }
    Ok(())
}
