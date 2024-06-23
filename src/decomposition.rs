use std::cmp::min;
use std::iter::FromIterator;

use handlegraph::{
    handle::{Direction, Edge, Handle, NodeId},
    handlegraph::{HandleGraph, IntoHandles, IntoNeighbors, IntoSequences},
    hashgraph::HashGraph,
};
use rustc_hash::{FxHashMap, FxHashSet};

use crate::*;

const MIN_COMPONENT_SIZE: usize = 5;

struct DecomposeGraph<'a> {
    graph: &'a HashGraph,
    id: FxHashMap<Handle, usize>,
    visited: Vec<bool>,
    parent: Vec<Option<usize>>,
    discovery_time: Vec<usize>,
    low: Vec<usize>,
    time: usize,
}

impl<'a> DecomposeGraph<'a> {
    fn find_articulation_points_rec(&mut self, u: Handle, j: usize, aps: &mut FxHashSet<Handle>) {
        self.visited[j] = true;
        self.discovery_time[j] = self.time.clone();
        self.low[j] = self.time.clone();
        self.time += 1;

        let mut children = 0;

        for v in self
            .graph
            .neighbors(u, Direction::Right)
            .chain(self.graph.neighbors(u, Direction::Left))
        {
            let i = self.id[&v.forward()];
            if !self.visited[i] {
                // DFS forward traversal
                self.parent[i] = Some(j);
                children += 1;
                self.find_articulation_points_rec(v, i, aps);
                self.low[j] = min(self.low[j], self.low[i]);
                if self.parent[j].is_some() && self.low[i] >= self.discovery_time[j] {
                    aps.insert(u.forward());
                }
            } else if Some(i) != self.parent[j] {
                // backward edge case
                self.low[j] = min(self.low[j], self.discovery_time[i]);
            }
        }
        if self.parent[j].is_none() && children > 1 {
            aps.insert(u.forward());
        }
    }

    fn find_articulation_points(&mut self) -> FxHashSet<Handle> {
        let mut res = FxHashSet::default();
        for v in self.graph.handles() {
            let i = self.id[&v];
            if !self.visited[i] {
                self.find_articulation_points_rec(v, i, &mut res);
            }
        }
        res
    }

    fn new(graph: &'a HashGraph) -> Self {
        let n = graph.node_count();
        DecomposeGraph {
            graph: graph,
            id: FxHashMap::from_iter(graph.handles().enumerate().map(|(i, v)| (v, i))),
            visited: vec![false; n],
            parent: vec![None; n],
            discovery_time: vec![n + 1; n],
            low: vec![n + 1; n],
            time: 0,
        }
    }
}

fn is_prefix_candidate(graph: &HashGraph, v: Handle) -> bool {
    // this function is not exact, as it does not take all parents of a collapsible prefix into
    // account, in other words, the function produces false positives, but never false negatives.
    let mut first_char: FxHashSet<u8> = FxHashSet::default();

    // traverse multifurcation in the forward direction of the handle
    for u in graph.neighbors(v, Direction::Right) {
        let mut c = graph.base(u, 0).unwrap();
        // make all letters uppercase
        if c >= 90 {
            c -= 32
        }
        if first_char.contains(&c) {
            return true;
        }
        first_char.insert(c);
    }
    false
}

fn check_collapsible(graph: &HashGraph, v: Handle) -> bool {

    is_prefix_candidate(graph, v) || graph.neighbors(v, Direction::Right).any(|u| is_prefix_candidate(graph, u.flip()))
}

pub fn assign_component(
    graph: &HashGraph,
    id: &FxHashMap<Handle, usize>,
    component: &mut Vec<Option<usize>>,
    end_points: &FxHashSet<Handle>,
    u: Handle,
    cid: usize,
) -> bool {
    let mut queue: Vec<Handle> = graph
        .neighbors(u, Direction::Right)
        .filter(|v| component[id[&v.forward()]].is_none() && !end_points.contains(&v.forward()))
        .collect();
    let mut is_nonempty = false;
    while !queue.is_empty() {
        let v = queue.pop().unwrap();
        let i = id[&v.forward()];
        match &component[i] {
            None => {
        component[i] = Some(cid);
        is_nonempty |= true;
        for u in graph.neighbors(v, Direction::Right).chain(graph.neighbors(v, Direction::Left).map(|u| u.flip())) {
            let j = id[&u.forward()];
            if !end_points.contains(&u.forward()) {
                if component[j].is_none() {
                    queue.push(u);
                } else {
                    assert!(component[j] == Some(cid), "assumed that all nodes within this component have same id")
                }
            }
        }
            },
            Some(cjd) => assert!(cjd == &cid, "visited node {} already is associated with component, contradicting initial assumption", v2str(&v))
        }
    }
    is_nonempty
}

fn components_to_subgraphs(
    graph: &HashGraph,
    id: &FxHashMap<Handle, usize>,
    n_comp: usize,
    component: &Vec<Option<usize>>,
) -> (Vec<HashGraph>, HashGraph) {
    let mut g_endpoints = HashGraph::new();
    let mut g_components: Vec<HashGraph> = (0..n_comp).map(|_| HashGraph::new()).collect();

    for v in graph.handles() {
        let i = id[&v];
        match component[i] {
            None => &mut g_endpoints,
            Some(cid) => &mut g_components[cid],
        }
        .create_handle(&graph.sequence_vec(v)[..], v.unpack_number());
    }
    for e in graph.edges() {
        let v = e.0.forward();
        let u = e.1.forward();
        let i = id[&v];
        let j = id[&u];
        match (component[i], component[j]) {
            (None, None) => g_endpoints.create_edge(e),
            (Some(c), None) => {
                if !g_components[c].has_node(u.id()) {
                    g_components[c].create_handle(&[b'*'], u.unpack_number());
                }
                g_components[c].create_edge(e);
            }
            (None, Some(c)) => {
                if !g_components[c].has_node(v.id()) {
                    g_components[c].create_handle(&[b'*'], v.unpack_number());
                }
                g_components[c].create_edge(e);
            }
            (Some(c), Some(d)) => {
                assert!(c == d, "assume that each edge is from the same component");
                g_components[c].create_edge(e);
            }
        }
    }
    (g_components, g_endpoints)
}

pub fn adjust_maxids(graphs: &mut Vec<HashGraph>, max_id: usize) {
    let mut id = max_id;
    for g in graphs {
        g.max_id = NodeId(id as u64);
        id += g.node_count();
    }
}

pub fn split_into_subgraphs(graph: HashGraph) -> (Vec<HashGraph>, HashGraph) {
    // dg must be mut, because find_articulation_points_() changes the state of the data structure
    let mut dg = DecomposeGraph::new(&graph);
    let aps: Vec<Handle> = dg
        .find_articulation_points()
        .into_iter()
        .filter(|v| { !check_collapsible(&graph, *v) && !check_collapsible(&graph, v.flip())
        })
        .collect();
    let ends: Vec<Handle> = graph
        .handles()
        .filter(|v| {
            (graph.degree(*v, Direction::Right) == 0 && !check_collapsible(&graph, v.flip())) || (graph.degree(*v, Direction::Left) == 0 && !check_collapsible(&graph, *v))
        })
        .collect();

    let mut starts: FxHashSet<Handle> = FxHashSet::default();
    let end_points: Vec<Handle> = ends.into_iter().chain(aps).collect();
    let end_points_set = FxHashSet::from_iter(end_points.iter().cloned());
    let mut component = vec![None; graph.node_count()];
    let mut c = 0;

    log::debug!(
        "end points: {}",
        end_points
            .iter()
            .map(v2str)
            .collect::<Vec<String>>()
            .join(", ")
    );
    for end_point in end_points.iter() {
        let i = dg.id[end_point];
        if assign_component(
            &graph,
            &dg.id,
            &mut component,
            &end_points_set,
            *end_point,
            c,
        ) {
            c += 1;
        }
        if assign_component(
            &graph,
            &dg.id,
            &mut component,
            &end_points_set,
            end_point.flip(),
            c,
        ) {
            c += 1;
        }
    }
    log::info!("identified {} independently collapsible components", c);
    assert!(graph.handles().all(|v| component[dg.id[&v]].is_some() || end_points.contains(&v)), "starting from end- and articulation points did not result in the exhaustive traversal of the graph");
    let (mut g_comps, g_ends) = components_to_subgraphs(&graph, &dg.id, c, &component);
    adjust_maxids(&mut g_comps, graph.max_id.0 as usize);
    (g_comps, g_ends)
}
