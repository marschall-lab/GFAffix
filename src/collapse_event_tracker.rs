use handlegraph::{
    handle::{Direction, Edge, Handle},
    handlegraph::{IntoNeighbors, IntoSequences},
    hashgraph::HashGraph,
    mutablehandlegraph::AdditiveHandleGraph,
};
use rustc_hash::{FxHashMap, FxHashSet};

/* project use */
use crate::v2str;

#[derive(Clone, Debug)]
pub struct CollapseEventTracker {
    // tranform from (node_id, node_len) -> [(node_id, node_orient, node_len), ..]
    //                ^ keys are always forward oriented
    pub transform: FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    pub overlapping_events: usize,
    pub bubbles: usize,
    pub events: usize,

    pub modified_nodes: FxHashSet<(usize, usize)>,
}

impl CollapseEventTracker {
    pub fn report(
        &mut self,
        collapsed_prefix_node: Handle,
        prefix_len: usize,
        splitted_node_pairs: &Vec<(usize, Direction, usize, Handle, Option<(Handle, usize)>)>,
    ) {
        self.events += 1;
        self.modified_nodes
            .insert((collapsed_prefix_node.unpack_number() as usize, prefix_len));
        let is_bubble = splitted_node_pairs.iter().all(|x| x.4.is_none());
        if is_bubble {
            self.bubbles += 1;
        }

        let prefix_id = collapsed_prefix_node.unpack_number() as usize;
        let prefix_orient = if collapsed_prefix_node.is_reverse() {
            Direction::Left
        } else {
            Direction::Right
        };
        for (node_id, node_orient, node_len, _, suffix) in splitted_node_pairs {
            // do not report transformations of the same node to itself or to its reverse
            if node_id != &prefix_id || node_len != &prefix_len {
                // record transformation of node, even if none took place (which is the case if node v
                // equals the dedicated shared prefix node
                let mut replacement: Vec<(usize, Direction, usize)> = Vec::new();
                replacement.push((prefix_id, prefix_orient, prefix_len));
                if let Some((v, vlen)) = suffix {
                    replacement.push((
                        v.unpack_number() as usize,
                        if v.is_reverse() {
                            Direction::Left
                        } else {
                            Direction::Right
                        },
                        *vlen,
                    ));
                    self.modified_nodes
                        .insert((v.unpack_number() as usize, *vlen));
                }

                // orient transformation
                // important notice:
                // - handle_graph::split_handle() works only in forward direction
                // - the first node of the split pair an will always be the node itself (again in
                //   forward direction)
                if *node_orient == Direction::Left {
                    replacement.reverse();
                    for r in replacement.iter_mut() {
                        r.1 = if r.1 == Direction::Left {
                            Direction::Right
                        } else {
                            Direction::Left
                        };
                    }
                }
                log::debug!(
                    "new replacement rule {}:{} -> {}",
                    node_id,
                    node_len,
                    replacement
                        .iter()
                        .map(|(rid, ro, rlen)| format!(
                            "{}{}:{}",
                            if *ro == Direction::Left { '<' } else { '>' },
                            rid,
                            rlen
                        ))
                        .collect::<Vec<String>>()
                        .join("")
                );
                self.transform
                    .insert((*node_id, *node_len), replacement.clone());
            }
        }
    }

    pub fn expand(
        &self,
        node_id: usize,
        node_orient: Direction,
        node_len: usize,
    ) -> Vec<(usize, Direction, usize)> {
        let mut res: Vec<(usize, Direction, usize)> = Vec::new();

        if self.transform.contains_key(&(node_id, node_len)) {
            for (rid, rorient, rlen) in self.transform.get(&(node_id, node_len)).unwrap() {
                // if identical node appears in its expansion sequence, don't expand...
                if (*rid, *rlen) != (node_id, node_len) {
                    res.extend(self.expand(*rid, *rorient, *rlen));
                } else {
                    res.push((*rid, *rorient, *rlen));
                }
            }
            if node_orient == Direction::Left {
                res.reverse();
                for x in res.iter_mut() {
                    x.1 = match x.1 {
                        Direction::Left => Direction::Right,
                        Direction::Right => Direction::Left,
                    };
                }
            }
        } else {
            res.push((node_id, node_orient, node_len));
        }

        res
    }

    pub fn deduplicate_transform(
        &mut self,
        node_id: usize,
        node_len: usize,
        copies: &mut FxHashMap<(usize, usize), Vec<Handle>>,
    ) {
        let mut queue = vec![(node_id, node_len)];

        while queue.len() > 0 {
            let (vid, vlen) = queue.pop().unwrap();
            if self.transform.contains_key(&(vid, vlen)) {
                let mut copy_of_vid = vid.clone();
                for (rid, _, rlen) in self.transform.get_mut(&(vid, vlen)).unwrap() {
                    let key = (rid.clone(), rlen.clone());
                    if copies.contains_key(&key) {
                        // replace by a copy
                        let c = copies.get_mut(&key).unwrap().pop();
                        if c == None {
                            panic!("not enough copies available for node {}:{} to deduplicate transformation rule of {}:{}", key.0, key.1, vid, vlen);
                        }
                        let rid_new = c.unwrap().unpack_number() as usize;
                        log::debug!("replace {}:{} by {}:{} in de-duplication of transformation rule of {}:{}", rid, rlen, rid_new, rlen, vid, vlen);
                        *rid = rid_new;

                        // if copy is also key of transform table, then record new ID
                        if key == (vid, vlen) {
                            copy_of_vid = rid.clone()
                        }
                    }
                    // if identical node appears in its expansion sequence, don't expand...
                    if (*rid, *rlen) != (copy_of_vid, vlen) {
                        queue.push((*rid, *rlen));
                    }
                }

                // if copy is also key of transform table, then update key
                if copies.contains_key(&(vid, vlen)) && copy_of_vid != vid {
                    let val = self.transform.remove(&(vid, vlen)).unwrap();
                    self.transform.insert((copy_of_vid, vlen.clone()), val);
                }
            }
        }
    }

    pub fn get_expanded_transformation(
        &self,
    ) -> FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>> {
        let mut res: FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>> =
            FxHashMap::default();
        res.reserve(self.transform.len());

        for (node_id, node_len) in self.transform.keys() {
            let expansion = self.expand(*node_id, Direction::Right, *node_len);
            log::debug!(
                "deep-expansion of walk {} of node {}:{} into {}",
                self.transform
                    .get(&(*node_id, *node_len))
                    .unwrap()
                    .iter()
                    .map(|(rid, ro, rlen)| format!(
                        "{}{}:{}",
                        if *ro == Direction::Left { '<' } else { '>' },
                        rid,
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join(""),
                node_id,
                node_len,
                expansion
                    .iter()
                    .map(|(rid, ro, rlen)| format!(
                        "{}{}:{}",
                        if *ro == Direction::Left { '<' } else { '>' },
                        rid,
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join("")
            );

            res.insert((*node_id, *node_len), expansion);
        }
        res
    }

    pub fn decollapse(&mut self, graph: &mut HashGraph, nodes: FxHashSet<(usize, usize)>) {
        // first of all, remove unnecessary transformation rules
        let keys = self
            .transform
            .keys()
            .map(|(xid, xlen)| (xid.clone(), xlen.clone()))
            .collect::<Vec<(usize, usize)>>();
        for (vid, vlen) in keys {
            let rule = self.transform.get(&(vid, vlen)).unwrap();
            if rule.len() == 1 && rule[0] == (vid, Direction::Right, vlen) {
                self.transform.remove(&(vid, vlen));
            }
        }
        let mut count: FxHashMap<(usize, usize), usize> = FxHashMap::default();
        for (vid, vlen) in nodes.iter() {
            let expansion = self.expand(*vid, Direction::Right, *vlen);

            for (uid, _, ulen) in expansion.iter() {
                *count.entry((*uid, *ulen)).or_insert(0) += 1;
            }
        }

        log::info!(
            "reverting {} collapses in order to de-duplicate nodes on given set of paths",
            count
                .values()
                .map(|&x| if x > 1 { 1 } else { 0 })
                .sum::<usize>()
        );

        // multiplicate nodes that occur more than once
        let mut copies: FxHashMap<(usize, usize), Vec<Handle>> = FxHashMap::default();
        for ((vid, vlen), occ) in count.iter_mut() {
            // if a duplicated node is hit, create and record as many copies as needed to
            // de-duplicate it!
            if *occ > 1 {
                // yes, the duplicated node is a valid copy of its own!
                copies
                    .entry((*vid, *vlen))
                    .or_insert(Vec::new())
                    .push(Handle::pack(*vid, false));
            }
            // make some more copies
            while *occ > 1 {
                // create copy u of node v
                let v = Handle::pack(*vid, false);
                let u = graph.append_handle(&graph.sequence_vec(v)[..]);
                log::debug!(
                    "creating duplicate {} of node {}",
                    u.unpack_number(),
                    v.unpack_number()
                );
                // copy incident edges of v onto u
                for w in graph.neighbors(v, Direction::Left).collect::<Vec<Handle>>() {
                    log::debug!(
                        "creating duplicate edge <{}{}",
                        u.unpack_number(),
                        v2str(&w)
                    );
                    graph.create_edge(Edge(u.flip(), w.flip()));
                }
                for w in graph
                    .neighbors(v, Direction::Right)
                    .collect::<Vec<Handle>>()
                {
                    log::debug!(
                        "creating duplicate edge >{}{}",
                        u.unpack_number(),
                        v2str(&w)
                    );
                    graph.create_edge(Edge(u, w));
                }
                copies.get_mut(&(*vid, *vlen)).unwrap().push(u);
                *occ -= 1
            }
        }

        // update transformation table
        for (vid, vlen) in nodes.iter() {
            self.deduplicate_transform(*vid, *vlen, &mut copies);
        }
    }

    pub fn new() -> Self {
        CollapseEventTracker {
            transform: FxHashMap::default(),
            overlapping_events: 0,
            bubbles: 0,
            events: 0,
            modified_nodes: FxHashSet::default(),
        }
    }
}
