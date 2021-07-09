/* standard use */
use std::cmp::Ordering;
use std::collections::VecDeque;
use std::error::Error;
use std::fs;
use std::io;
use std::io::prelude::*;
use std::str::{self, FromStr};

/* crate use */
use clap::Clap;
use gfa::{
    gfa::{orientation::Orientation, GFA},
    parser::GFAParser,
};
use handlegraph::{
    handle::{Direction, Edge, Handle},
    handlegraph::*,
    hashgraph::HashGraph,
    mutablehandlegraph::{AdditiveHandleGraph, MutableHandles},
    pathhandlegraph::GraphPathNames,
};
use quick_csv::Csv;
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;

#[derive(clap::Clap, Debug)]
#[clap(
    version = "0.1",
    author = "Daniel Doerr <daniel.doerr@hhu.de>",
    about = "Discover path-preserving shared prefixes in multifurcations of a given graph.\n
    - Do you want log output? Call program with 'RUST_LOG=info gfaffix ...'
    - Log output not informative enough? Try 'RUST_LOG=debug gfaffix ...'"
)]
pub struct Command {
    #[clap(index = 1, about = "graph in GFA1 format", required = true)]
    pub graph: String,

    #[clap(
        short = 'o',
        long = "output_refined",
        about = "write refined graph in GFA1 format to supplied file",
        default_value = " "
    )]
    pub refined_graph_out: String,

    #[clap(
        short = 't',
        long = "output_transformation",
        about = "report original nodes and their corresponding paths in refined graph to supplied file",
        default_value = " "
    )]
    pub transformation_out: String,

    #[clap(
        short = 'c',
        long = "check_transformation",
        about = "Verifies that the transformed parts of the graphs spell out the identical sequence as in the original graph. Only for debugging purposes."
    )]
    pub check_transformation: bool,

    #[clap(
        short = 'x',
        long = "dont_collapse",
        about = "Do not collapse nodes on a given set of paths",
        default_value = " "
    )]
    pub no_collapse_path: Vec<String>,
}

// structure for storing reported subgraph
pub struct AffixSubgraph {
    pub sequence: String,
    pub parents: Vec<Handle>,
    pub shared_prefix_nodes: Vec<Handle>,
}

#[derive(Clone, Debug)]
pub struct DeletedSubGraph {
    pub nodes: FxHashSet<Handle>,
}

impl DeletedSubGraph {
    fn add(&mut self, v: Handle) -> bool {
        if v.is_reverse() {
            self.nodes.insert(v.flip())
        } else {
            self.nodes.insert(v)
        }
    }

    fn edge_deleted(&self, u: &Handle, v: &Handle) -> bool {
        let mut res: bool;
        if u.is_reverse() {
            res = self.nodes.contains(&u.flip());
        } else {
            res = self.nodes.contains(u);
        }
        if v.is_reverse() {
            res |= self.nodes.contains(&v.flip())
        } else {
            res |= self.nodes.contains(v)
        }
        res
    }

    fn node_deleted(&self, v: &Handle) -> bool {
        if v.is_reverse() {
            self.nodes.contains(&v.flip())
        } else {
            self.nodes.contains(v)
        }
    }

    fn new() -> Self {
        DeletedSubGraph {
            nodes: FxHashSet::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CollapseEventTracker {
    // tranform from (node_id, node_len) -> [(node_id, node_orient, node_len), ..]
    //                ^ keys are always forward oriented
    pub transform: FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    pub overlapping_events: usize,
    pub bubbles: usize,
    pub events: usize,

    modified_nodes: FxHashSet<(usize, usize)>,
}

impl CollapseEventTracker {
    fn report(
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

    fn expand(
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

    fn deduplicate_transform(
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

    fn get_expanded_transformation(
        &self,
    ) -> FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>> {
        let mut res: FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>> =
            FxHashMap::default();
        res.reserve(self.transform.len());

        for (node_id, node_len) in self.transform.keys() {
            let expansion = self.expand(*node_id, Direction::Right, *node_len);
            log::debug!(
                "deep-expansion of path {} of node {}:{} into {}",
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

    fn decollapse(&mut self, graph: &mut HashGraph, nodes: FxHashSet<(usize, usize)>) {
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
                        "creating duplicate edge <{}{}{}",
                        u.unpack_number(),
                        if w.is_reverse() { '<' } else { '>' },
                        w.unpack_number()
                    );
                    graph.create_edge(Edge(u.flip(), w.flip()));
                }
                for w in graph
                    .neighbors(v, Direction::Right)
                    .collect::<Vec<Handle>>()
                {
                    log::debug!(
                        "creating duplicate edge >{}{}{}",
                        u.unpack_number(),
                        if w.is_reverse() { '<' } else { '>' },
                        w.unpack_number()
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

    fn new() -> Self {
        CollapseEventTracker {
            transform: FxHashMap::default(),
            overlapping_events: 0,
            bubbles: 0,
            events: 0,
            modified_nodes: FxHashSet::default(),
        }
    }
}

fn enumerate_path_preserving_shared_affixes(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    v: Handle,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    let mut res: Vec<AffixSubgraph> = Vec::new();

    let mut branch: FxHashMap<(u8, Vec<Handle>), Vec<Handle>> = FxHashMap::default();
    // traverse multifurcation in the forward direction of the handle
    for u in graph.neighbors(v, Direction::Right) {
        if !del_subg.node_deleted(&u) {
            // get parents of u
            let mut parents: Vec<Handle> = graph
                .neighbors(u, Direction::Left)
                .filter(|w| !del_subg.node_deleted(&w))
                .collect();
            parents.sort();
            // insert child in path-preserving data structure
            let mut c = graph.base(u, 0).unwrap();
            // make all letters uppercase
            if c >= 90 {
                c -= 32
            }
            branch.entry((c, parents)).or_insert(Vec::new()).push(u);
        }
    }

    for ((c, parents), children) in branch.iter() {
        if children.len() > 1 && (c == &b'A' || c == &b'C' || c == &b'G' || c == &b'T') {
            let prefix = get_shared_prefix(children, graph)?;
            log::debug!(
                "identified shared prefix {} between nodes {} originating from parent(s) {}",
                if prefix.len() > 10 {
                    prefix[..10].to_string() + "..."
                } else {
                    prefix.clone()
                },
                children
                    .iter()
                    .map(|v| format!(
                        "{}{}",
                        if v.is_reverse() { '<' } else { '>' },
                        v.unpack_number()
                    ))
                    .collect::<Vec<String>>()
                    .join(","),
                parents
                    .iter()
                    .map(|v| format!(
                        "{}{}",
                        if v.is_reverse() { '<' } else { '>' },
                        v.unpack_number()
                    ))
                    .collect::<Vec<String>>()
                    .join(",")
            );
            res.push(AffixSubgraph {
                sequence: prefix,
                parents: parents.clone(),
                shared_prefix_nodes: children.clone(),
            });
        }
    }

    Ok(res)
}

fn collapse(
    graph: &mut HashGraph,
    shared_prefix: &AffixSubgraph,
    del_subg: &mut DeletedSubGraph,
    event_tracker: &mut CollapseEventTracker,
) -> Handle {
    let prefix_len = shared_prefix.sequence.len();

    // Sort handles with shared prefix so that reversed ones come first! This is important for the
    // case that two shared prefixes correspond to the same node, one in forward, and one in
    // backward dirction (e.g. >1209, <1209 share prefix 'C'). In those cases, the code that splits
    // handles only works iff the backward oriented handle is split first (e.g., <1209 is split
    // into <329203 and <1209) and then the forward oriented handle (e.g., truncated handle >1209
    // is split into >1209 and 329204), Subsequently, either >1209 or >329203 is deleted, with the
    // other being advanced as dedicated shared prefix node.

    let mut shared_prefix_nodes = shared_prefix.shared_prefix_nodes.clone();
    shared_prefix_nodes.sort_by(|x, y| match (x.is_reverse(), y.is_reverse()) {
        (true, false) => Ordering::Less,
        (false, true) => Ordering::Greater,
        _ => Ordering::Equal,
    });

    // update graph in two passes:
    //  1. split handles into shared prefix and distinct suffix and appoint dedicated shared
    //  prefix node
    let mut shared_prefix_node_pos: usize = 0;
    // each element in splitted_node_pairs is of the form:
    //  1. node ID of original handle
    //  2. direction of original handle
    //  3. length of original handle
    //  4-5. splitted handle (IMPORTANT: that's generally not equivalent with the replacement
    //  handles!)
    let mut splitted_node_pairs: Vec<(usize, Direction, usize, Handle, Option<(Handle, usize)>)> =
        Vec::new();
    for (i, v) in shared_prefix_nodes.iter().enumerate() {
        let v_len = graph.node_len(*v);
        let node_id = v.unpack_number() as usize;
        let node_orient = if v.is_reverse() {
            Direction::Left
        } else {
            Direction::Right
        };
        if v_len > prefix_len {
            // x corresponds to the shared prefix,
            let (x, u) = if v.is_reverse() {
                // apparently, rs-handlegraph does not allow splitting nodes in reverse direction
                let (u_rev, x_rev) = graph.split_handle(v.flip(), v_len - prefix_len);
                (x_rev.flip(), u_rev.flip())
            } else {
                graph.split_handle(*v, prefix_len)
            };
            splitted_node_pairs.push((
                node_id,
                node_orient,
                v_len,
                x,
                Some((u, graph.node_len(u))),
            ));
            // update dedicated shared prefix node if none has been assigned yet
            log::debug!(
                "splitting node {}{} into prefix {}{} and suffix {}{}",
                if v.is_reverse() { '<' } else { '>' },
                v.unpack_number(),
                if x.is_reverse() { '<' } else { '>' },
                x.unpack_number(),
                if u.is_reverse() { '<' } else { '>' },
                u.unpack_number()
            );
        } else {
            // always use a node as dedicated shared prefix node if that node coincides with the
            // prefix
            shared_prefix_node_pos = i;
            splitted_node_pairs.push((node_id, node_orient, v_len, *v, None));
            log::debug!(
                "node {}{} matches prefix {}",
                if v.is_reverse() { '<' } else { '>' },
                v.unpack_number(),
                &shared_prefix.sequence
            );
        }
    }

    //  2. update deleted edge set, reassign outgoing edges of "empty" nodes to dedicated shared
    //     prefix node
    // there will be always a shared prefix node, so this condition is always true
    let shared_prefix_split = splitted_node_pairs[shared_prefix_node_pos];
    let shared_prefix_node = shared_prefix_split.3;
    log::debug!(
        "node {}{} is dedicated shared prefix node",
        if shared_prefix_node.is_reverse() {
            '<'
        } else {
            '>'
        },
        shared_prefix_node.unpack_number()
    );

    for (_, _, _, u, maybe_v) in splitted_node_pairs.iter() {
        if *u != shared_prefix_node {
            // rewrire outgoing edges
            match maybe_v {
                Some((v, _)) => {
                    // make all suffixes spring from shared suffix node
                    if !graph.has_edge(shared_prefix_node, *v) {
                        graph.create_edge(Edge(shared_prefix_node, *v));
                        log::debug!(
                            "create edge {}{}{}{}",
                            if shared_prefix_node.is_reverse() {
                                '<'
                            } else {
                                '>'
                            },
                            shared_prefix_node.unpack_number(),
                            if v.is_reverse() { '<' } else { '>' },
                            v.unpack_number(),
                        );
                    }
                }
                None => {
                    // if node coincides with shared prefix (but is not the dedicated shared prefix
                    // node), then all outgoing edges of this node must be transferred to dedicated
                    // node
                    let outgoing_edges: Vec<Handle> = graph
                        .neighbors(*u, Direction::Right)
                        .filter(|v| !del_subg.edge_deleted(&u, v))
                        .collect();
                    for x in outgoing_edges {
                        if !graph.has_edge(shared_prefix_node, x) {
                            graph.create_edge(Edge(shared_prefix_node, x));
                            log::debug!(
                                "create edge {}{}{}{}",
                                if shared_prefix_node.is_reverse() {
                                    '<'
                                } else {
                                    '>'
                                },
                                shared_prefix_node.unpack_number(),
                                if x.is_reverse() { '<' } else { '>' },
                                x.unpack_number(),
                            );
                        }
                    }
                }
            }
            // mark redundant node as deleted
            log::debug!(
                "flag {}{} as deleted",
                if u.is_reverse() { '<' } else { '>' },
                u.unpack_number()
            );
            del_subg.add(*u);
        }
    }

    event_tracker.report(
        shared_prefix_node,
        graph.node_len(shared_prefix_node),
        &splitted_node_pairs,
    );
    shared_prefix_node
}

fn get_shared_prefix(
    nodes: &Vec<Handle>,
    graph: &HashGraph,
) -> Result<String, std::string::FromUtf8Error> {
    let mut seq: Vec<u8> = Vec::new();

    let sequences: Vec<Vec<u8>> = nodes.iter().map(|v| graph.sequence_vec(*v)).collect();

    let mut i = 0;
    while sequences[0].len() > i {
        let c: u8 = sequences[0][i];

        if sequences.iter().any(|other| {
            other.len() <= i
                || match (other[i], c) {
                    (b'A', b'A') => false,
                    (b'A', b'a') => false,
                    (b'a', b'A') => false,
                    (b'a', b'a') => false,
                    (b'C', b'C') => false,
                    (b'C', b'c') => false,
                    (b'c', b'C') => false,
                    (b'c', b'c') => false,
                    (b'G', b'G') => false,
                    (b'G', b'g') => false,
                    (b'g', b'G') => false,
                    (b'g', b'g') => false,
                    (b'T', b'T') => false,
                    (b'T', b't') => false,
                    (b't', b'T') => false,
                    (b't', b't') => false,
                    _ => true,
                }
        }) {
            break;
        }
        seq.push(c);
        i += 1;
    }

    String::from_utf8(seq)
}

fn find_and_collapse_path_preserving_shared_affixes<W: Write>(
    graph: &mut HashGraph,
    out: &mut io::BufWriter<W>,
) -> (DeletedSubGraph, CollapseEventTracker) {
    let mut del_subg = DeletedSubGraph::new();

    let mut event_tracker = CollapseEventTracker::new();

    let mut has_changed = true;
    while has_changed {
        has_changed = false;
        let mut queue: VecDeque<Handle> = VecDeque::new();
        queue.extend(graph.handles().chain(graph.handles().map(|v| v.flip())));
        while let Some(v) = queue.pop_front() {
            if !del_subg.node_deleted(&v) {
                log::debug!(
                    "processing oriented node {}{}",
                    if v.is_reverse() { '<' } else { '>' },
                    v.unpack_number()
                );

                // process node in forward direction
                let affixes =
                    enumerate_path_preserving_shared_affixes(graph, &del_subg, v).unwrap();
                for affix in affixes.iter() {
                    has_changed |= true;
                    // in each iteration, the set of deleted nodes can change and affect the
                    // subsequent iteration, so we need to check the status the node every time
                    if affix
                        .shared_prefix_nodes
                        .iter()
                        .chain(affix.parents.iter())
                        .any(|u| del_subg.node_deleted(u))
                    {
                        // push non-deleted parents back on queue
                        queue.extend(affix.parents.iter().filter(|u| !del_subg.node_deleted(u)));
                    } else {
                        print(affix, out).unwrap();
                        if affix
                            .parents
                            .iter()
                            .chain(affix.shared_prefix_nodes.iter())
                            .any(|&u| {
                                event_tracker
                                    .modified_nodes
                                    .contains(&(u.unpack_number() as usize, graph.node_len(u)))
                            })
                        {
                            event_tracker.overlapping_events += 1
                        }
                        let shared_prefix_node =
                            collapse(graph, affix, &mut del_subg, &mut event_tracker);
                        queue.push_back(shared_prefix_node);
                        queue.push_back(shared_prefix_node.flip());
                    }
                }
            }
        }
    }

    log::info!(
        "identified {} shared prefixes, {} of which are overlapping, and {} of which are bubbles",
        event_tracker.events,
        event_tracker.overlapping_events,
        event_tracker.bubbles
    );
    (del_subg, event_tracker)
}

fn transform_path(
    path: &Vec<(usize, Direction, usize)>,
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
) -> Vec<(usize, Direction)> {
    let mut res: Vec<(usize, Direction)> = Vec::new();

    for (sid, o, slen) in path.iter() {
        match transform.get(&(*sid, *slen)) {
            Some(us) => res.extend(match o {
                Direction::Right => us
                    .iter()
                    .map(|(x, y, _)| (*x, *y))
                    .collect::<Vec<(usize, Direction)>>(),
                Direction::Left => us
                    .iter()
                    .rev()
                    .map(|(x, y, _)| {
                        (
                            *x,
                            if *y == Direction::Left {
                                Direction::Right
                            } else {
                                Direction::Left
                            },
                        )
                    })
                    .collect::<Vec<(usize, Direction)>>(),
            }),
            None => res.push((*sid, *o)),
        }
    }

    res
}

fn print_active_subgraph<W: io::Write>(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    writeln!(out, "H\tVN:Z:1.0")?;
    for v in graph.handles() {
        if !del_subg.node_deleted(&v) {
            writeln!(
                out,
                "S\t{}\t{}",
                v.unpack_number(),
                String::from_utf8(graph.sequence_vec(v))?
            )?;
        }
    }

    for Edge(mut u, mut v) in graph.edges() {
        if u.is_reverse() && v.is_reverse() {
            let w = u.flip();
            u = v.flip();
            v = w;
        }
        if !del_subg.edge_deleted(&u, &v) {
            writeln!(
                out,
                "L\t{}\t{}\t{}\t{}\t0M",
                u.unpack_number(),
                if u.is_reverse() { '-' } else { '+' },
                v.unpack_number(),
                if v.is_reverse() { '-' } else { '+' }
            )?;
        }
    }
    Ok(())
}

fn check_transform(
    old_graph: &HashGraph,
    new_graph: &HashGraph,
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
) {
    for ((vid, vlen), path) in transform.iter() {
        let path_len: usize = path.iter().map(|x| x.2).sum();
        if *vlen != path_len {
            panic!(
                "length of path {} does not sum up to that of its replacing node of {}:{}",
                path.iter()
                    .map(|(rid, ro, rlen)| format!(
                        "{}{}:{}",
                        if *ro == Direction::Left { '<' } else { '>' },
                        rid,
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join(""),
                vid,
                vlen
            );
        }

        let v = Handle::pack(*vid, false);
        if old_graph.has_node(v.id()) && old_graph.node_len(v) == *vlen {
            let old_seq = old_graph.sequence_vec(v);
            let new_seq = spell_walk(new_graph, path);
            if old_seq != new_seq {
                panic!(
                    "node {} in old graph spells sequence {}, but walk {} in new graph spell sequence {}", 
                    vid,
                    String::from_utf8(old_seq).unwrap(),
                    path.iter()
                        .map(|(rid, ro, _)| format!(
                                "{}{}",
                                if *ro == Direction::Left { '<' } else { '>' },
                        rid,))
                        .collect::<Vec<String>>()
                        .join(""), 
                    String::from_utf8(new_seq).unwrap()
                    );
            }
        }
    }
}

fn print_transformations<W: Write>(
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    orig_node_lens: &FxHashMap<usize, usize>,
    out: &mut io::BufWriter<W>,
) -> Result<(), io::Error> {
    writeln!(
        out,
        "{}",
        ["original_node", "transformed_path", "bp_length"].join("\t")
    )?;

    for ((vid, vlen), path) in transform.iter() {
        if match orig_node_lens.get(vid) {
            Some(l) => l == vlen,
            _ => false,
        } && (path.len() > 1 || *vid != path[0].0)
        {
            writeln!(
                out,
                "{}\t{}\t{}",
                vid,
                path.iter()
                    .map(|(rid, ro, _)| format!(
                        "{}{}",
                        if *ro == Direction::Left { '<' } else { '>' },
                        rid,
                    ))
                    .collect::<Vec<String>>()
                    .join(""),
                vlen
            )?;
        }
    }
    Ok(())
}

fn spell_walk(graph: &HashGraph, walk: &Vec<(usize, Direction, usize)>) -> Vec<u8> {
    let mut res: Vec<u8> = Vec::new();

    let mut prev_v: Option<Handle> = None;
    for (i, (sid, o, _)) in walk.iter().enumerate() {
        let v = Handle::pack(*sid, *o != Direction::Right);
        if i >= 1 && !graph.has_edge(prev_v.unwrap(), v) {
            panic!("graph does not have edge {:?}-{:?}", &walk[i - 1], &walk[i]);
        }
        res.extend(graph.sequence_vec(v));
        prev_v = Some(v);
    }
    res
}

fn print<W: io::Write>(affix: &AffixSubgraph, out: &mut io::BufWriter<W>) -> Result<(), io::Error> {
    let parents: Vec<String> = affix
        .parents
        .iter()
        .map(|&v| {
            format!(
                "{}{}",
                if v.is_reverse() { '<' } else { '>' },
                v.unpack_number(),
            )
        })
        .collect();
    let children: Vec<String> = affix
        .shared_prefix_nodes
        .iter()
        .map(|&v| {
            format!(
                "{}{}",
                if v.is_reverse() { '<' } else { '>' },
                v.unpack_number(),
            )
        })
        .collect();
    writeln!(
        out,
        "{}\t{}\t{}\t{}",
        parents.join(","),
        children.join(","),
        affix.sequence.len(),
        &affix.sequence,
    )?;
    Ok(())
}

fn parse_and_transform_paths<W: io::Write>(
    gfa: &GFA<usize, ()>,
    orig_node_lens: &FxHashMap<usize, usize>,
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    for path in gfa.paths.iter() {
        log::debug!("transforming path {}", str::from_utf8(&path.path_name)?);
        let tpath = transform_path(
            &path
                .iter()
                .map(|(sid, o)| {
                    (
                        sid,
                        match o {
                            Orientation::Forward => Direction::Right,
                            Orientation::Backward => Direction::Left,
                        },
                        *orig_node_lens.get(&sid).unwrap(),
                    )
                })
                .collect(),
            &transform,
        );
        writeln!(
            out,
            "P\t{}\t{}\t{}",
            str::from_utf8(&path.path_name)?,
            tpath
                .iter()
                .map(|(sid, o)| format!(
                    "{}{}",
                    sid,
                    if *o == Direction::Right { '+' } else { '-' }
                ))
                .collect::<Vec<String>>()
                .join(","),
            path.overlaps
                .iter()
                .map(|x| match x {
                    None => "*".to_string(),
                    Some(c) => c.to_string(),
                })
                .collect::<Vec<String>>()
                .join("")
        )?;
    }

    Ok(())
}

fn parse_and_transform_walks<W: io::Write, R: io::Read>(
    mut data: io::BufReader<R>,
    //    graph: &HashGraph,
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    orig_node_lens: &FxHashMap<usize, usize>,
    //    del_subg: &DeletedSubGraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    let reader = Csv::from_reader(&mut data)
        .delimiter(b'\t')
        .flexible(true)
        .has_header(false);

    for row in reader.into_iter() {
        let row = row.unwrap();
        let mut row_it = row.bytes_columns();

        if &[b'W'] == row_it.next().unwrap() {
            let sample_id = str::from_utf8(row_it.next().unwrap())?;
            let hap_idx = str::from_utf8(row_it.next().unwrap())?;
            let seq_id = str::from_utf8(row_it.next().unwrap())?;
            let seq_start = str::from_utf8(row_it.next().unwrap())?;
            let seq_end = str::from_utf8(row_it.next().unwrap())?;
            let walk_ident = format!(
                "{}#{}#{}:{}-{}",
                sample_id, hap_idx, seq_id, seq_start, seq_end
            );
            log::debug!("transforming walk {}", walk_ident);

            let walk_data = row_it.next().unwrap();
            let mut walk: Vec<(usize, Direction, usize)> = Vec::new();

            let mut cur_el: Vec<u8> = Vec::new();
            for c in walk_data {
                if (c == &b'>' || c == &b'<') && !cur_el.is_empty() {
                    let sid = usize::from_str(str::from_utf8(&cur_el[1..])?)?;
                    let o = match cur_el[0] {
                        b'>' => Direction::Right,
                        b'<' => Direction::Left,
                        _ => panic!(
                            "unknown orientation '{}' of segment {} in walk {}",
                            cur_el[0], sid, walk_ident
                        ),
                    };
                    walk.push((sid, o, *orig_node_lens.get(&sid).unwrap()));
                    cur_el.clear();
                }
                cur_el.push(*c);
            }

            if !cur_el.is_empty() {
                let sid = usize::from_str(str::from_utf8(&cur_el[1..])?)?;
                let o = match cur_el[0] {
                    b'>' => Direction::Right,
                    b'<' => Direction::Left,
                    _ => panic!(
                        "unknown orientation '{}' of segment {} in walk {}",
                        cur_el[0], sid, walk_ident
                    ),
                };
                walk.push((sid, o, *orig_node_lens.get(&sid).unwrap()));
            }

            let tpath = transform_path(&walk, &transform);
            //            check_path(graph, del_subg, &tpath);
            writeln!(
                out,
                "W\t{}\t{}\t{}\t{}\t{}\t{}",
                sample_id,
                hap_idx,
                seq_id,
                seq_start,
                seq_end,
                tpath
                    .iter()
                    .map(|(sid, o)| format!(
                        "{}{}",
                        if *o == Direction::Right { '>' } else { '<' },
                        sid
                    ))
                    .collect::<Vec<String>>()
                    .join("")
            )?;
        }
    }

    Ok(())
}

fn main() -> Result<(), io::Error> {
    env_logger::init();

    // print output to stdout
    let mut out = io::BufWriter::new(std::io::stdout());

    // initialize command line parser & parse command line arguments
    let params = Command::parse();

    log::info!("loading graph {}", &params.graph);
    let parser = GFAParser::new();
    let gfa: GFA<usize, ()> = parser.parse_file(&params.graph).unwrap();

    log::info!("constructing handle graph");
    let mut graph = HashGraph::from_gfa(&gfa);

    log::info!(
        "handlegraph has {} nodes and {} edges",
        graph.node_count(),
        graph.edge_count()
    );

    log::info!("storing length of original nodes for bookkeeping");
    let mut node_lens: FxHashMap<usize, usize> = FxHashMap::default();
    node_lens.reserve(graph.node_count());
    for v in graph.handles() {
        node_lens.insert(v.unpack_number() as usize, graph.node_len(v));
    }

    let mut dont_collapse_nodes: FxHashSet<(usize, usize)> = FxHashSet::default();
    for path_str in params.no_collapse_path {
        if !path_str.trim().is_empty() {
            if !graph.has_path(&path_str.as_bytes()[..]) {
                panic!("unknown path {}", path_str);
            }
            let path_id = graph.get_path_id(&path_str.as_bytes()[..]).unwrap();
            let path = graph.get_path(&path_id).unwrap();
            dont_collapse_nodes.extend(path.nodes.iter().map(|&x| {
                let xid = x.unpack_number() as usize;
                (xid, *node_lens.get(&xid).unwrap())
            }));

            log::info!(
                "flagging nodes of path {} as non-collapsing, total number is now at {}",
                path_str,
                dont_collapse_nodes.len()
            );
        }
    }

    //
    // REMOVING PATHS FROM GRAPH -- they SUBSTANTIALLY slow down graph editing
    //
    graph.paths.clear();

    log::info!("identifying path-preserving shared prefixes");
    writeln!(
        out,
        "{}",
        [
            "oriented_parent_nodes",
            "oriented_child_nodes",
            "prefix_length",
            "prefix",
        ]
        .join("\t")
    )?;

    let (del_subg, mut event_tracker) =
        find_and_collapse_path_preserving_shared_affixes(&mut graph, &mut out);

    if dont_collapse_nodes.len() > 0 {
        log::info!("de-collapse no-collapse handles and update transformation table");
        event_tracker.decollapse(&mut graph, dont_collapse_nodes);
    }

    log::info!("expand transformation table");
    let transform = event_tracker.get_expanded_transformation();

    if params.check_transformation {
        log::info!("checking correctness of applied transformations...");
        let old_graph = HashGraph::from_gfa(&gfa);
        check_transform(&old_graph, &graph, &transform);
        log::info!("all correct!");
    }

    if !params.transformation_out.trim().is_empty() {
        log::info!("writing transformations to {}", params.transformation_out);
        let mut trans_out =
            io::BufWriter::new(fs::File::create(params.transformation_out.clone())?);
        if let Err(e) = print_transformations(&transform, &node_lens, &mut trans_out) {
            panic!("unable to write graph transformations to stdout: {}", e);
        }
    }

    if !params.refined_graph_out.trim().is_empty() {
        log::info!("writing refined graph to {}", params.refined_graph_out);
        let mut graph_out = io::BufWriter::new(fs::File::create(params.refined_graph_out.clone())?);
        if let Err(e) = print_active_subgraph(&graph, &del_subg, &mut graph_out) {
            panic!(
                "unable to write refined graph to {}: {}",
                params.refined_graph_out.clone(),
                e
            );
        }
        log::info!("transforming paths");
        if let Err(e) = parse_and_transform_paths(&gfa, &node_lens, &transform, &mut graph_out) {
            panic!(
                "unable to write refined GFA path lines to {}: {}",
                params.refined_graph_out.clone(),
                e
            );
        };
        log::info!("transforming walks");
        let data = io::BufReader::new(fs::File::open(&params.graph)?);
        if let Err(e) = parse_and_transform_walks(data, &transform, &node_lens, &mut graph_out) {
            panic!(
                "unable to parse or write refined GFA walk lines  to {}: {}",
                params.refined_graph_out.clone(),
                e
            );
        }
    }
    out.flush()?;
    log::info!("done");
    Ok(())
}
