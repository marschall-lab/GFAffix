use std::collections::HashSet;

use handlegraph::{
    handle::{Direction, Edge, Handle},
    handlegraph::{IntoNeighbors, IntoSequences},
    hashgraph::HashGraph,
    mutablehandlegraph::AdditiveHandleGraph,
};
use rustc_hash::{FxHashMap, FxHashSet};

/* project use */
use crate::deleted_sub_graph::DeletedSubGraph;
use crate::{v2str, v2tuple, FxIndexMap, FxIndexSet};

#[derive(Debug)]
pub struct CollapseEventTracker<'a> {
    // tranform from (node_id, node_len) -> [(node_id, node_orient, node_len), ..]
    //                ^ keys are always forward oriented
    pub transform: FxIndexMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    // if there are non-collapse nodes that could be nevertheless collapsed (and then must be
    // de-collapsed in a subsequent step, we need to know these nodes, also those that are
    // constructed during de-collapse. If they are eventually
    // collapsed, we record their incident edges for the decollapse procedure
    pub dont_collapse_nodes: &'a mut FxIndexSet<(usize, usize)>,
    pub dont_collapse_nodes_lastorig: Option<(usize, usize)>,
    //   key: original node--because trait struct Direction does not support the Hash trait, we
    //        need to store the orientation as boolean, indicating whether the node is reversed
    //        (=>true)
    // value: right-side neighboring original nodes
    pub dont_collapse_edges: FxHashMap<(usize, bool, usize), Vec<(usize, Direction, usize)>>,
    //   key: original node--because trait struct Direction does not support the Hash trait, we
    //        need to store the orientation as boolean, indicating whether the node is reversed
    //        (=>true)
    // value: group identifier
    pub dont_collapse_siblings_group: FxHashMap<(usize, bool, usize), usize>,
    // For each group (identifier == position), a list of siblings is stored that have been jointly
    // collappsed. These can be used in combination with dont_collapse_edges to restore the
    // original edes of the graph
    pub dont_collapse_siblings_members: Vec<Vec<(usize, Direction, usize)>>,
    pub overlapping_events: usize,
    pub bubbles: usize,
    pub events: usize,

    pub modified_nodes: FxHashSet<(usize, usize)>,
}

impl<'a> CollapseEventTracker<'a> {
    pub fn retain_dont_collapse_edges(
        &mut self,
        original_blunt_edges: Vec<((usize, Direction, usize), Vec<(usize, Direction, usize)>)>,
    ) {
        log::debug!(
            "storing right-side edges of to-be-collapsed siblings {}",
            original_blunt_edges
                .iter()
                .map(|(v, es)| format!(
                    "{}{}:{}--{{{}}}",
                    match v.1 {
                        Direction::Left => "<",
                        Direction::Right => ">",
                    },
                    v.0,
                    v.2,
                    es.iter()
                        .map(|u| format!(
                            "{}{}:{}",
                            match u.1 {
                                Direction::Left => "<",
                                Direction::Right => ">",
                            },
                            u.0,
                            u.2
                        ))
                        .collect::<Vec<String>>()
                        .join(",")
                ))
                .collect::<Vec<String>>()
                .join(", ")
        );
        // TODO describe what you do here
        if !self.dont_collapse_nodes.is_empty() && !original_blunt_edges.is_empty() {
            let group_id = self.dont_collapse_siblings_members.len();
            self.dont_collapse_siblings_members
                .push(original_blunt_edges.iter().map(|(x, _)| *x).collect());
            for ((vid, vorient, vlen), es) in original_blunt_edges {
                let v = (vid, vorient == Direction::Left, vlen);
                self.dont_collapse_edges.insert(v, es);
                self.dont_collapse_siblings_group.insert(v, group_id);
            }
        }
    }

    pub fn report(
        &mut self,
        collapsed_prefix_node: Handle,
        prefix_len: usize,
        splitted_node_pairs: &Vec<(usize, Direction, usize, Handle, Option<(Handle, usize)>)>,
    ) {
        self.events += 1;

        let prefix_id = collapsed_prefix_node.unpack_number() as usize;
        let prefix_orient = if collapsed_prefix_node.is_reverse() {
            Direction::Left
        } else {
            Direction::Right
        };

        self.modified_nodes.insert((prefix_id, prefix_len));

        let is_bubble = splitted_node_pairs.iter().all(|x| x.4.is_none());
        if is_bubble {
            self.bubbles += 1;
        }

        for (node_id, node_orient, node_len, _node_handle, suffix) in splitted_node_pairs {
            // record transformation of node, even if none took place (which is the case if node v
            // equals the dedicated shared prefix node, but make sure it's then in synced
            // orientation
            let mut replacement: Vec<(usize, Direction, usize)> = vec![(
                prefix_id,
                if node_id == &prefix_id && node_len == &prefix_len {
                    *node_orient
                } else {
                    prefix_orient
                },
                prefix_len,
            )];
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

    pub fn get_collapsed_nodes(
        &self,
        graph: &HashGraph,
        del_subg: &DeletedSubGraph,
    ) -> Vec<((usize, usize), (usize, usize))> {
        // returns a list of (duplicated node, rule)-tuples that are sorted in the order in which the de-collapse must be carried out
        let mut locus_tags: FxHashMap<(usize, usize), Vec<(usize, usize)>> = FxHashMap::default();

        for v in self.dont_collapse_nodes.iter() {
            // remember that transform is an FxIndexMap, so, we are iterating through transform in
            // the order in which the nodes were added
            if self.transform.contains_key(v) {
                for u in self.expand(v.0, Direction::Right, v.1) {
                    let u_handle = Handle::pack(u.0, false);
                    locus_tags
                        .entry((u.0, u.2))
                        .or_insert_with(|| Vec::new())
                        .push((v.0, v.1));
                }
            }
            // only iterate over original nodes
            // unwrap() works here somewhat safely (*if used correctly*), because if one can
            // iterate over dont_collapse_nodes, the list must have a last element in its original
            // form
            if v == &self.dont_collapse_nodes_lastorig.unwrap() {
                break;
            }
        }

        let mut counts: FxHashMap<(usize, usize), usize> = FxHashMap::default();

        let mut rules_with_dupls: FxHashMap<(usize, usize), Vec<(usize, usize)>> =
            FxHashMap::default();
        for (dupl, rules) in locus_tags {
            if rules.len() > 1 {
                log::debug!(
                    "node >{}:{} shares {} collapsed reference locations: {}",
                    dupl.0,
                    dupl.1,
                    rules.len(),
                    rules
                        .iter()
                        .map(|x| format!(">{}:{}", x.0, x.1))
                        .collect::<Vec<String>>()
                        .join(", ")
                );
                counts.insert(dupl, rules.len());
                for rule in rules {
                    // it's not possible to de-collapse an "identity" transformation rule
                    if rule.0 != dupl.0 && rule.1 != dupl.1 {
                        rules_with_dupls
                            .entry(rule)
                            .or_insert(Vec::new())
                            .push(dupl);
                    }
                }
            }
        }

        let mut res: Vec<((usize, usize), (usize, usize))> = Vec::new();
        for (v, rule) in self.transform.iter() {
            if let Some(dupls) = rules_with_dupls.get(v).cloned() {
                for dupl in dupls {
                    for u in rule {
                        if counts[&dupl] > 1 {
                            if u.0 == dupl.0 && u.2 == dupl.1 {
                                res.push((dupl, *v));
                                counts.entry(dupl).and_modify(|c| *c -= 1);
                            } else {
                                rules_with_dupls
                                    .entry((u.0, u.2))
                                    .or_insert(Vec::new())
                                    .push(dupl);
                            }
                        }
                    }
                }
            }
        }
        assert!(
            counts.values().all(|x| *x == 1),
            "get_collapsed_nodes produced either too many decollapses or to few: \n{}",
            counts
                .iter()
                .filter_map(|(k, v)| match *v {
                    1 => None,
                    _ => Some(format!(">{}:{} = {}", k.0, k.1, v)),
                })
                .collect::<Vec<String>>()
                .join("\n")
        );
        res.reverse();
        res
    }

    pub fn decollapse(
        &mut self,
        graph: &mut HashGraph,
        del_subg: &mut DeletedSubGraph,
    ) -> Vec<usize> {
        let node2rule = self.get_collapsed_nodes(graph, del_subg);
        let mut decollapse_count = 0;
        let mut decollapsed_blunt_siblings: FxHashMap<(usize, usize), FxHashSet<usize>> =
            FxHashMap::default();
        for ((vid, vlen), u) in node2rule.into_iter() {
            match self.transform[&u][..] {
                [(wid, worient, wlen)] => {
                    assert!(
                        vid == wid && vlen == wlen,
                        "expected rule >{}:{} -> {}{}{} to point at duplicate {}{}:{}",
                        u.0,
                        u.1,
                        match worient {
                            Direction::Right => ">",
                            Direction::Left => "<",
                        },
                        wid,
                        wlen,
                        // yeah, we are going to re-use the orientation of node w for this message
                        match worient {
                            Direction::Right => ">",
                            Direction::Left => "<",
                        },
                        vid,
                        vlen
                    );

                    log::debug!(
                        "decollapsing transform >{}:{} -> {}{}:{}",
                        u.0,
                        u.1,
                        match worient {
                            Direction::Right => ">",
                            Direction::Left => "<",
                        },
                        wid,
                        wlen,
                    );

                    let y = self.decollapse_blunt_node(
                        (wid, worient, wlen),
                        u,
                        &mut decollapsed_blunt_siblings
                            .entry((vid, vlen))
                            .or_insert_with(|| FxHashSet::default()),
                        graph,
                        del_subg,
                    );
                    // update
                    log::debug!(
                        "++ updating transform to >{}:{} -> {}:{}",
                        u.0,
                        u.1,
                        v2str(&y),
                        wlen
                    );
                    self.transform.insert(
                        u,
                        vec![
                            // the new created node has always right direction
                            (y.unpack_number() as usize, Direction::Right, wlen),
                        ],
                    );
                }
                [(wid, worient, wlen), (xid, xorient, xlen)] => {
                    log::debug!(
                        "decollapsing transform >{}:{} -> {}{}:{}{}{}:{}",
                        u.0,
                        u.1,
                        match worient {
                            Direction::Right => ">",
                            Direction::Left => "<",
                        },
                        wid,
                        wlen,
                        match xorient {
                            Direction::Right => ">",
                            Direction::Left => "<",
                        },
                        xid,
                        xlen
                    );

                    // observe that duplicated nodes are always *prefix*, in the sense that
                    // relative to their orientation, to their left is the parent node
                    // whose children shared some prefixes, and to their right comes the
                    // un-shared suffix
                    if wid == vid && wlen == vlen {
                        // make sure the suffix node is *real*
                        let (oid, oorient, olen) = (xid, xorient, xlen);
                        let (xid, xorient, xlen) = self.expand(xid, xorient, xlen)[0];
                        let y = self.decollapse_prefix(
                            (wid, worient, wlen),
                            (xid, xorient, xlen),
                            graph,
                            del_subg,
                        );
                        // update transformation table to de-duplicate rule
                        log::debug!(
                            "++ updating transform to >{}:{} -> {}:{}{}{}:{} ",
                            u.0,
                            u.1,
                            v2str(&y),
                            wlen,
                            match oorient {
                                Direction::Right => ">",
                                Direction::Left => "<",
                            },
                            oid,
                            olen
                        );
                        // update transform
                        self.transform.entry(u).and_modify(|x| {
                            x[0] = (y.unpack_number() as usize, Direction::Right, wlen)
                        });
                    } else {
                        assert!(
                            vid == xid && vlen == xlen,
                            "expected duplicated node >{}:{} at 2nd position, but found >{}:{}",
                            vid,
                            vlen,
                            xid,
                            xlen
                        );
                        // make sure the suffix node is *real*
                        let (oid, oorient, olen) = (wid, worient, wlen);
                        let (wid, worient, wlen) =
                            self.expand(wid, worient, wlen).last().unwrap().clone();
                        // either the rule is in forward direction (then it is covered by
                        // the if-case), or it is in reverse direction (else)
                        let y = self.decollapse_prefix(
                            (
                                xid,
                                match xorient {
                                    Direction::Left => Direction::Right,
                                    Direction::Right => Direction::Left,
                                },
                                xlen,
                            ),
                            (
                                wid,
                                match worient {
                                    Direction::Left => Direction::Right,
                                    Direction::Right => Direction::Left,
                                },
                                wlen,
                            ),
                            graph,
                            del_subg,
                        );
                        // update transformation table to de-duplicate rule
                        log::debug!(
                            "++ updating transform to >{}:{}-> {}{}:{}{}:{}",
                            u.0,
                            u.1,
                            match oorient {
                                Direction::Right => ">",
                                Direction::Left => "<",
                            },
                            oid,
                            olen,
                            v2str(&y.flip()),
                            xlen
                        );
                        // update transform
                        self.transform.entry(u).and_modify(|x| {
                            x[1] = (y.unpack_number() as usize, Direction::Left, xlen)
                        });
                    }
                }
                [] | [_, _, _, ..] => unreachable!(),
            }
        }

        log::info!("decollapsed {} nodes", decollapse_count);
        let mut res = Vec::new();

        res
    }

    fn decollapse_prefix(
        &self,
        u: (usize, Direction, usize),
        v: (usize, Direction, usize),
        graph: &mut HashGraph,
        del_subg: &mut DeletedSubGraph,
    ) -> Handle {
        let (uid, uorient, ulen) = u;
        let u = Handle::pack(uid, uorient == Direction::Left);
        let (vid, vorient, vlen) = v;
        let v = Handle::pack(vid, vorient == Direction::Left);

        // assumes that the original node is split into two parts, where the first part, u, must
        // now be de-collapsed.
        let mut w = graph.append_handle(&graph.sequence_vec(u)[..]);
        log::debug!("++ creating duplicate {} of node {}", v2str(&w), v2str(&u),);
        // copy left-incident edges of u onto w

        for x in graph.neighbors(u, Direction::Left).collect::<Vec<Handle>>() {
            if !del_subg.edge_deleted(&x, &u) {
                log::debug!(
                    "++ creating duplicate {}{} of edge {}{}",
                    v2str(&x),
                    v2str(&w),
                    v2str(&x),
                    v2str(&u),
                );
                let e = Edge::edge_handle(x, w);
                graph.create_edge(e);
            }
        }

        log::debug!(
            "++ creating duplicate {}{} of edge {}{}",
            v2str(&w),
            v2str(&v),
            v2str(&u),
            v2str(&v),
        );

        graph.create_edge(Edge::edge_handle(w, v));

        //        log::debug!("flagging edge {}{} as deleted during decollapse of node {}", v2str(&u), v2str(&v), v2str(&u));
        //        del_subg.add_edge(Edge::edge_handle(u, v));

        w
    }

    pub fn decollapse_blunt_node(
        &self,
        v: (usize, Direction, usize),
        u: (usize, usize),
        decollapsed_blunt_siblings: &mut FxHashSet<usize>,
        graph: &mut HashGraph,
        del_subg: &mut DeletedSubGraph,
    ) -> Handle {
        let mut v = Handle::pack(v.0, v.1 == Direction::Left);
        let (uid, ulen) = u;
        let mut u = Handle::pack(uid, false);
        let mut x = graph.append_handle(&graph.sequence_vec(v)[..]);
        let xlen = graph.node_len(x);
        log::debug!(
            "++ creating duplicate {} of node >{}:{}",
            v2str(&x),
            uid,
            ulen
        );

        assert!(
            xlen == ulen,
            "length ({}) of decollapsed node {} does not match original node {} (length {})",
            xlen,
            v2str(&x),
            v2str(&u),
            ulen
        );

        let mut recovered_sides = [false, false];
        for (s, uorient) in [(0, Direction::Right), (1, Direction::Left)] {
            // 1. left direction is processed last; flip orientation of decollapsed node to match that of the
            //    original
            if uorient == Direction::Left {
                x = x.flip();
                v = v.flip();
                u = u.flip();
            }
            if let Some(group_id) =
                self.dont_collapse_siblings_group
                    .get(&(uid, uorient == Direction::Left, ulen))
            {
                recovered_sides[s] |= true;
                log::debug!(
                    "++ recovering child edges outgoing of \"{}\"",
                    match uorient {
                        Direction::Right => ">",
                        Direction::Left => "<",
                    }
                );

                let mut keep_neighbors: HashSet<Handle> = HashSet::default();
                for (i, s) in self.dont_collapse_siblings_members[*group_id]
                    .iter()
                    .enumerate()
                {
                    if s == &(uid, uorient, ulen) {
                        for (yid, yorient, ylen) in self.dont_collapse_edges
                            [&(uid, uorient == Direction::Left, ulen)]
                            .iter()
                        {
                            // get transformed neighbor
                            let (yid, yorient, ylen) = self.expand(*yid, *yorient, *ylen)[0];
                            // What if neighboring edge points back to original node?
                            let y = if yid == uid {
                                Handle::pack(x.unpack_number(), yorient != uorient)
                            } else {
                                Handle::pack(yid, yorient == Direction::Left)
                            };
                            log::debug!(
                                "++ creating duplicate {}{} of edge {}{}",
                                v2str(&x),
                                v2str(&y),
                                v2str(&u),
                                v2str(&y),
                            );
                            let e = Edge::edge_handle(x, y);
                            graph.create_edge(e);
                            // duplicate delete flags *from prefix node v*
                            if del_subg.edge_deleted(&v, &y) {
                                del_subg.add_edge(e);
                            }
                            // report original node as decollapsed--this is important if the very same prefix
                            // needs to be decollapsed even further (but then these edges must be taken into
                            // account in the separation process
                            decollapsed_blunt_siblings.insert(i);
                        }
                    } else if !decollapsed_blunt_siblings.contains(&i) {
                        let neighbors: Vec<Handle> = self.dont_collapse_edges
                            [&(s.0, s.1 == Direction::Left, s.2)]
                            .iter()
                            .map(|(yid, yorient, ylen)| {
                                let (yid, yorient, ylen) = self.expand(*yid, *yorient, *ylen)[0];
                                // this is about *keeping* edges, so if the neighboring edge
                                // points back to the original node, it's just fine
                                Handle::pack(yid, yorient == Direction::Left)
                            })
                            .collect();

                        log::debug!(
                            "++ keeping edges {} at original node",
                            neighbors
                                .iter()
                                .map(v2str)
                                .collect::<Vec<String>>()
                                .join(",")
                        );

                        keep_neighbors.extend(neighbors);
                    }
                }

                // observe that v as already been flipped, so we are looking at the right(!) direction
                for w in graph.neighbors(v, Direction::Right) {
                    if !keep_neighbors.contains(&w) && !del_subg.node_deleted(&w) {
                        log::debug!(
                            "++ flagging edge {}{} as deleted during decollapse of node {}",
                            v2str(&v),
                            v2str(&w),
                            v2str(&v),
                        );
                        del_subg.add_edge(Edge::edge_handle(v, w));
                    }
                }
            }
        }

        // recover other side
        for (i, is_recovered) in IntoIterator::into_iter(recovered_sides).enumerate() {
            if !is_recovered {
                log::debug!(
                    "++ recovering parental edges outgoing of \"{}\"",
                    if i == 0 { ">" } else { "<" }
                );

                // observe that x is already flipped in second iteration of previous loop
                for w in graph.neighbors(v, Direction::Left).collect::<Vec<Handle>>() {
                    if !del_subg.node_deleted(&w) {
                        log::debug!("++ recovering parental edge {}{}", v2str(&w), v2str(&x));
                        let e = Edge::edge_handle(w, x);
                        if !graph.has_edge(w, x) {
                            graph.create_edge(e);
                        }
                    }
                }
            }
            v = v.flip();
            x = x.flip();
        }

        // duplicate delete flags
        if del_subg.node_deleted(&v) {
            del_subg.add_node(x);
        }
        x.flip()
    }

    pub fn new(dont_collapse_nodes: &'a mut FxIndexSet<(usize, usize)>) -> Self {
        let last = dont_collapse_nodes.iter().last().cloned();
        CollapseEventTracker {
            transform: FxIndexMap::default(),
            dont_collapse_nodes: dont_collapse_nodes,
            dont_collapse_nodes_lastorig: last,
            dont_collapse_edges: FxHashMap::default(),
            dont_collapse_siblings_group: FxHashMap::default(),
            dont_collapse_siblings_members: Vec::new(),
            overlapping_events: 0,
            bubbles: 0,
            events: 0,
            modified_nodes: FxHashSet::default(),
        }
    }

    //    pub fn merge(event_trackers: Vec<Self>) -> Self {
    //        assert!(
    //            event_trackers.len() > 0,
    //            "assumed non-empty list of event trackers"
    //        );
    //        let mut res =
    //            CollapseEventTracker::new(event_trackers.first().unwrap().dont_collapse_nodes);
    //
    //        for x in event_trackers {
    //            assert!(
    //                x.transform.keys().all(|x| !res.transform.contains_key(x)),
    //                "assumed transformations are disjoint"
    //            );
    //            res.transform.extend(x.transform.into_iter());
    //            res.dont_collapse_edges
    //                .extend(x.dont_collapse_edges.into_iter());
    //            res.dont_collapse_siblings_group
    //                .extend(x.dont_collapse_siblings_group.into_iter());
    //            res.dont_collapse_siblings_members
    //                .extend(x.dont_collapse_siblings_members.into_iter());
    //            res.overlapping_events += x.overlapping_events;
    //            res.bubbles += x.bubbles;
    //            res.events += x.events;
    //            res.modified_nodes.extend(x.modified_nodes.into_iter());
    //        }
    //
    //        res
    //    }
}
