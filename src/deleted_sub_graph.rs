use handlegraph::handle::{Edge, Handle};
use rustc_hash::FxHashSet;

#[derive(Clone, Debug)]
pub struct DeletedSubGraph {
    pub nodes: FxHashSet<Handle>,
    pub edges: FxHashSet<Edge>,
}

impl DeletedSubGraph {
    pub fn add_node(&mut self, v: Handle) -> bool {
        if v.is_reverse() {
            self.nodes.insert(v.flip())
        } else {
            self.nodes.insert(v)
        }
    }

    pub fn add_edge(&mut self, e: Edge) -> bool {
        self.edges.insert(e)
    }

    pub fn edge_deleted(&self, u: &Handle, v: &Handle) -> bool {
        let mut res = self.edges.contains(&Edge::edge_handle(*u, *v));
        res |= if u.is_reverse() {
            self.nodes.contains(&u.flip())
        } else {
            self.nodes.contains(u)
        };
        if v.is_reverse() {
            res |= self.nodes.contains(&v.flip());
        } else {
            res |= self.nodes.contains(v);
        }
        res
    }

    pub fn node_deleted(&self, v: &Handle) -> bool {
        if v.is_reverse() {
            self.nodes.contains(&v.flip())
        } else {
            self.nodes.contains(v)
        }
    }

    pub fn new() -> Self {
        DeletedSubGraph {
            nodes: FxHashSet::default(),
            edges: FxHashSet::default(),
        }
    }

    pub fn merge(del_subgs: Vec<Self>) -> Self{
        let mut res = DeletedSubGraph::new();

        for x in del_subgs {
            res.nodes.extend(x.nodes);
            res.edges.extend(x.edges);
        }
        res
    }
}
