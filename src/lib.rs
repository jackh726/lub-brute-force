//! Graph generation and utilities for LUB coercion fuzzing.
//!
//! This library provides functions to generate all valid deref and unsizing
//! coercion graphs with specified constraints.

use itertools::Itertools;
use std::collections::HashSet;

pub type NodeId = usize;

/// Compressed Sparse Row (CSR) graph representation.
/// Reduces memory indirection compared to Vec<Vec<NodeId>>.
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub struct Graph {
    n: usize,
    // Layout: [offset_0, offset_1, ..., offset_n, edge_0, edge_1, ..., edge_m]
    data: Vec<usize>,
}

impl Graph {
    /// Creates a new empty graph with `n` nodes.
    pub fn new(n: usize) -> Self {
        let data = vec![0; n + 1];
        Self { n, data }
    }

    /// Converts an adjacency list to CSR format.
    pub fn from_adj_list(adj: Vec<Vec<NodeId>>) -> Self {
        let n = adj.len();
        let total_edges: usize = adj.iter().map(|neighbors| neighbors.len()).sum();

        let mut data = Vec::with_capacity(n + 1 + total_edges);
        data.push(0);

        let mut edge_count = 0;
        for neighbors in &adj {
            edge_count += neighbors.len();
            data.push(edge_count);
        }

        for neighbors in adj {
            data.extend(neighbors);
        }

        Self { n, data }
    }

    pub fn to_adj_list(&self) -> Vec<Vec<NodeId>> {
        (0..self.n)
            .map(|node| self.neighbors(node).to_vec())
            .collect()
    }

    /// Returns the neighbors of a node.
    pub fn neighbors(&self, node: NodeId) -> &[NodeId] {
        let start = self.data[node];
        let end = self.data[node + 1];
        &self.data[self.n + 1 + start..self.n + 1 + end]
    }

    /// Returns the number of nodes in the graph.
    pub fn len(&self) -> usize {
        self.n
    }

    /// Adds an edge from `from` to `to`.
    pub fn push_edge(&mut self, from: NodeId, to: NodeId) {
        let insert_pos = self.n + 1 + self.data[from + 1];
        self.data.insert(insert_pos, to);
        for i in (from + 1)..=self.n {
            self.data[i] += 1;
        }
    }

    /// Removes the last edge added from `from`.
    pub fn pop_edge(&mut self, from: NodeId) {
        if self.data[from + 1] > self.data[from] {
            let remove_pos = self.n + 1 + self.data[from + 1] - 1;
            self.data.remove(remove_pos);
            for i in (from + 1)..=self.n {
                self.data[i] -= 1;
            }
        }
    }
}

/// Checks if a graph is weakly connected (connected when treating edges as undirected).
pub fn is_weakly_connected(n: usize, edges: &[(NodeId, NodeId)]) -> bool {
    if n == 0 {
        return true;
    }
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

/// Generates all valid deref coercion graphs.
///
/// Constraints:
/// - Each node has at most one outgoing deref edge
/// - Graph is weakly connected
/// - No self-loops
pub fn generate_deref_graphs(n: usize) -> Vec<Graph> {
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
                graphs.push(Graph::from_adj_list(graph));
            }
        }
    }
    graphs
}

/// Generates all valid unsizing coercion graphs.
///
/// Constraints:
/// - Graph is a DAG (no cycles)
/// - Graph is weakly connected
/// - No self-loops
pub fn generate_unsizing_graphs(n: usize) -> Vec<Graph> {
    let mut graphs = HashSet::new();
    let all_edges: Vec<_> = (0..n)
        .cartesian_product(0..n)
        .filter(|(from, to)| from != to)
        .collect();

    fn backtrack(
        idx: usize,
        edges: &[(NodeId, NodeId)],
        graph: &mut Graph,
        graphs: &mut HashSet<Graph>,
        n: usize,
    ) {
        if !has_cycle(graph) {
            let edge_list: Vec<_> = (0..n)
                .flat_map(|i| graph.neighbors(i).iter().map(move |&j| (i, j)))
                .collect();
            if is_weakly_connected(n, &edge_list) {
                graphs.insert(graph.clone());
            }
        } else {
            return;
        }

        for i in idx..edges.len() {
            let (from, to) = edges[i];
            graph.push_edge(from, to);
            backtrack(i + 1, edges, graph, graphs, n);
            graph.pop_edge(from);
        }
    }

    let mut graph = Graph::new(n);
    backtrack(0, &all_edges, &mut graph, &mut graphs, n);
    graphs.into_iter().collect()
}

/// Detects if a directed graph contains a cycle.
pub fn has_cycle(graph: &Graph) -> bool {
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
        for &next in graph.neighbors(node) {
            if dfs(next, graph, state) {
                return true;
            }
        }
        state[node] = 2;
        false
    }

    (0..n).any(|i| dfs(i, graph, &mut state))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_deref_graphs_no_multi_out_edges() {
        for n in 2..=4 {
            let graphs = generate_deref_graphs(n);
            for graph in &graphs {
                for node in 0..graph.len() {
                    assert!(
                        graph.neighbors(node).len() <= 1,
                        "Node has multiple outgoing deref edges"
                    );
                }
            }
        }
    }

    #[test]
    fn test_deref_graphs_weakly_connected() {
        for n in 2..=4 {
            let graphs = generate_deref_graphs(n);
            for graph in &graphs {
                let edges: Vec<_> = (0..n)
                    .flat_map(|i| graph.neighbors(i).iter().map(move |&j| (i, j)))
                    .collect();
                assert!(
                    is_weakly_connected(n, &edges),
                    "Deref graph not weakly connected"
                );
            }
        }
    }

    #[test]
    fn test_deref_graphs_no_self_loops() {
        for n in 2..=4 {
            let graphs = generate_deref_graphs(n);
            for graph in &graphs {
                for i in 0..graph.len() {
                    assert!(
                        !graph.neighbors(i).contains(&i),
                        "Self-loop found in deref graph"
                    );
                }
            }
        }
    }

    #[test]
    fn test_unsizing_graphs_no_cycles() {
        for n in 2..=3 {
            let graphs = generate_unsizing_graphs(n);
            for graph in &graphs {
                assert!(!has_cycle(graph), "Cycle found in unsizing graph");
            }
        }
    }

    #[test]
    fn test_unsizing_graphs_weakly_connected() {
        for n in 2..=3 {
            let graphs = generate_unsizing_graphs(n);
            for graph in &graphs {
                let edges: Vec<_> = (0..n)
                    .flat_map(|i| graph.neighbors(i).iter().map(move |&j| (i, j)))
                    .collect();
                assert!(
                    is_weakly_connected(n, &edges),
                    "Unsizing graph not weakly connected"
                );
            }
        }
    }

    #[test]
    fn test_unsizing_graphs_no_self_loops() {
        for n in 2..=3 {
            let graphs = generate_unsizing_graphs(n);
            for graph in &graphs {
                for i in 0..graph.len() {
                    assert!(
                        !graph.neighbors(i).contains(&i),
                        "Self-loop found in unsizing graph"
                    );
                }
            }
        }
    }

    #[test]
    fn test_small_deref_graph_count() {
        assert_eq!(generate_deref_graphs(2).len(), 2); // empty or 0->1 or 1->0
        let graphs_3 = generate_deref_graphs(3);
        assert!(
            graphs_3.len() > 0,
            "Should generate some 3-node deref graphs"
        );
    }

    #[test]
    fn test_cycle_detection() {
        let no_cycle = Graph::from_adj_list(vec![vec![1], vec![2], vec![]]);
        assert!(!has_cycle(&no_cycle));

        let with_cycle = Graph::from_adj_list(vec![vec![1], vec![2], vec![0]]);
        assert!(has_cycle(&with_cycle));

        let self_loop = Graph::from_adj_list(vec![vec![0]]);
        assert!(has_cycle(&self_loop));
    }
}
