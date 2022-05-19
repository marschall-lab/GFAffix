use handlegraph::handle::Handle;
use rustc_hash::FxHashSet;

#[derive(Clone, Debug)]
pub struct DeletedSubGraph {
    pub nodes: FxHashSet<Handle>,
}

impl DeletedSubGraph {
    pub fn add_node(&mut self, v: Handle) -> bool {
        if v.is_reverse() {
            self.nodes.insert(v.flip())
        } else {
            self.nodes.insert(v)
        }
    }

    pub fn edge_deleted(&self, u: &Handle, v: &Handle) -> bool {
        let mut res = if u.is_reverse() {
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
        }
    }
}
