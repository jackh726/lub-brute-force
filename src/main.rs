use lub_fuzz::*;
use std::collections::HashMap;

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Adjustment {
    path: Vec<(NodeId, EdgeType)>,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq, Hash)]
enum EdgeType {
    Deref,
    Unsize,
}

fn find_lub(
    nodes: &[NodeId],
    deref: &Graph,
    unsize: &Graph,
) -> HashMap<NodeId, (NodeId, Adjustment)> {
    let mut results = HashMap::new();
    use std::collections::HashSet;

    for &node in nodes {
        let mut reachable = HashSet::new();
        let mut queue = vec![(node, vec![])];

        while let Some((current, path)) = queue.pop() {
            if !reachable.insert(current) {
                continue;
            }

            for &next in &deref[current] {
                let mut new_path = path.clone();
                new_path.push((current, EdgeType::Deref));
                queue.push((next, new_path));
            }
            for &next in &unsize[current] {
                let mut new_path = path.clone();
                new_path.push((current, EdgeType::Unsize));
                queue.push((next, new_path));
            }
        }

        let lub = *reachable.iter().max().unwrap_or(&node);
        results.insert(node, (lub, Adjustment { path: vec![] }));
    }

    results
}

fn main() {
    use itertools::Itertools;

    for n in 3..=5 {
        println!("Testing with {} nodes", n);

        let deref_graphs = generate_deref_graphs(n);
        let unsize_graphs = generate_unsizing_graphs(n);

        println!("  Deref graphs: {}", deref_graphs.len());
        println!("  Unsize graphs: {}", unsize_graphs.len());
        println!(
            "  Total pairs: {}",
            deref_graphs.len() * unsize_graphs.len()
        );

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

                let mismatch = orderings[1..]
                    .iter()
                    .any(|ordering| find_lub(ordering, deref, unsize) != first);

                if mismatch {
                    println!("\n!!! MISMATCH FOUND !!!");
                    println!("Deref graph #{}: {:?}", di, deref);
                    println!("Unsize graph #{}: {:?}", ui, unsize);
                    let results: Vec<_> = orderings
                        .iter()
                        .map(|ordering| (ordering, find_lub(ordering, deref, unsize)))
                        .collect();
                    for (ordering, result) in results {
                        println!("  Ordering: {:?}", ordering);
                        println!("  Result: {:?}", result);
                    }
                }
            }
        }
    }
}
