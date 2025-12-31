use itertools::Itertools;
use std::collections::{HashMap, HashSet};

type NodeId = usize;
type Graph = Vec<Vec<NodeId>>;

fn is_weakly_connected(n: usize, edges: &[(NodeId, NodeId)]) -> bool {
    let mut adj = vec![vec![]; n];
    for &(from, to) in edges {
        adj[from].push(to);
        adj[to].push(from);
    }
    let mut visited = vec![false; n];
    let mut stack = vec![0];
    visited[0] = true;
    while let Some(node) = stack.pop() {
        for &neighbor in &adj[node] {
            if !visited[neighbor] {
                visited[neighbor] = true;
                stack.push(neighbor);
            }
        }
    }
    visited.iter().all(|&v| v)
}

fn generate_deref_graphs(n: usize) -> Vec<Graph> {
    let mut graphs = vec![];
    let max_edges = n - 1;

    for num_edges in 0..=max_edges {
        for edge_set in (0..n).combinations(num_edges) {
            for targets in (0..n).combinations_with_replacement(num_edges) {
                let edges: Vec<_> = edge_set
                    .iter()
                    .zip(&targets)
                    .map(|(&from, &to)| (from, to))
                    .filter(|(from, to)| from != to)
                    .collect();

                if edges.len() != num_edges {
                    continue;
                }

                let mut out_degree = vec![0; n];
                for &(from, _) in &edges {
                    out_degree[from] += 1;
                    if out_degree[from] > 1 {
                        break;
                    }
                }
                if out_degree.iter().any(|&d| d > 1) {
                    continue;
                }
                if !is_weakly_connected(n, &edges) {
                    continue;
                }

                let mut graph = vec![vec![]; n];
                for (from, to) in edges {
                    graph[from].push(to);
                }
                graphs.push(graph);
            }
        }
    }
    graphs
}

fn generate_unsizing_graphs(n: usize) -> Vec<Graph> {
    let mut graphs = vec![];

    for num_edges in 0..=(n * (n - 1)) {
        for edges in (0..n)
            .cartesian_product(0..n)
            .filter(|(from, to)| from != to)
            .combinations(num_edges)
        {
            let edge_vec: Vec<_> = edges.iter().copied().collect();
            if !is_weakly_connected(n, &edge_vec) {
                continue;
            }

            let mut graph = vec![vec![]; n];
            for (from, to) in edge_vec {
                graph[from].push(to);
            }

            if has_cycle(&graph) {
                continue;
            }
            graphs.push(graph);
        }
    }
    graphs
}

fn has_cycle(graph: &Graph) -> bool {
    let n = graph.len();
    let mut state = vec![0u8; n];

    fn dfs(node: NodeId, graph: &Graph, state: &mut [u8]) -> bool {
        if state[node] == 1 {
            return true;
        }
        if state[node] == 2 {
            return false;
        }
        state[node] = 1;
        for &next in &graph[node] {
            if dfs(next, graph, state) {
                return true;
            }
        }
        state[node] = 2;
        false
    }

    (0..n).any(|i| dfs(i, graph, &mut state))
}

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
    for n in 3..=5 {
        println!("Testing with {} nodes", n);

        let deref_graphs = generate_deref_graphs(n);
        let unsize_graphs = generate_unsizing_graphs(n);

        println!("  Deref graphs: {}", deref_graphs.len());
        println!("  Unsize graphs: {}", unsize_graphs.len());

        for (di, deref) in deref_graphs.iter().enumerate() {
            for (ui, unsize) in unsize_graphs.iter().enumerate() {
                let orderings: Vec<Vec<_>> = (0..n).permutations(n).collect();

                let results: Vec<_> = orderings
                    .iter()
                    .map(|ordering| (ordering, find_lub(ordering, deref, unsize)))
                    .collect();

                let first_result = &results[0].1;
                if results.iter().any(|(_, r)| r != first_result) {
                    println!("\n!!! MISMATCH FOUND !!!");
                    println!("Deref graph #{}: {:?}", di, deref);
                    println!("Unsize graph #{}: {:?}", ui, unsize);
                    for (ordering, result) in results {
                        println!("  Ordering: {:?}", ordering);
                        println!("  Result: {:?}", result);
                    }
                }
            }
        }
    }
}
