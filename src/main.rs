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
use regex::Regex;
use rustc_hash::{FxHashMap, FxHashSet};

#[derive(clap::Clap, Debug)]
#[clap(
    version = "0.1.3",
    author = "Daniel Doerr <daniel.doerr@hhu.de>",
    about = "Discover walk-preserving shared prefixes in multifurcations of a given graph.\n
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
        about = "report original nodes and their corresponding walks in refined graph to supplied file",
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
        about = "Do not collapse nodes on a given paths (\"P\" lines) that match given regular expression",
        default_value = " "
    )]
    pub no_collapse_path: String,
}

// structure for storing reported subgraph
pub struct AffixSubgraph {
    pub sequence: String,
    pub parents: Vec<Handle>,
    pub shared_prefix_nodes: Vec<Handle>,
}

#[derive(Clone, Debug)]
pub struct ModifiedSubGraph {
    pub del_nodes: FxHashSet<Handle>,
    pub add_nodes: FxHashSet<Handle>,
    pub add_edges: FxHashSet<(Handle, Handle)>,
}

impl ModifiedSubGraph {
    fn record_deleted(&mut self, v: Handle) -> bool {
        self.del_nodes.insert(v.forward())
    }

    fn record_added(&mut self, v: Handle) -> bool {
        self.add_nodes.insert(v.forward())
    }

    fn record_added_edge(&mut self, u: Handle, v: Handle) -> bool {
        let e = vec![(u, v), (v, u), (u.flip(), v.flip()), (v.flip(), u.flip())]
            .into_iter()
            .min()
            .unwrap();
        self.add_edges.insert(e)
    }

    fn edge_deleted(&self, u: &Handle, v: &Handle) -> bool {
        self.node_deleted(u) || self.node_deleted(v)
    }

    fn node_deleted(&self, v: &Handle) -> bool {
        self.del_nodes.contains(&v.forward())
    }

    fn edge_added(&self, u: Handle, v: Handle) -> bool {
        let e = vec![(u, v), (v, u), (u.flip(), v.flip()), (v.flip(), u.flip())]
            .into_iter()
            .min()
            .unwrap();
        self.add_edges.contains(&e)
    }

    fn node_added(&self, v: &Handle) -> bool {
        self.add_nodes.contains(&v.forward())
    }

    fn new() -> Self {
        ModifiedSubGraph {
            add_nodes: FxHashSet::default(),
            add_edges: FxHashSet::default(),
            del_nodes: FxHashSet::default(),
        }
    }
}

#[derive(Clone, Debug)]
pub struct CollapseEventTracker {
    // tranform from (node_id, node_len) -> [(node_id, node_orient, node_len), ..]
    //                ^ keys are always forward oriented
    pub transform: FxHashMap<(Handle, usize), Vec<(Handle, usize)>>,
    pub overlapping_events: usize,
    pub bubbles: usize,
    pub events: usize,

    modified_nodes: FxHashSet<(Handle, usize)>,
}

impl CollapseEventTracker {
    fn report(
        &mut self,
        collapsed_prefix_node: Handle,
        prefix_len: usize,
        splitted_node_pairs: &Vec<(Handle, usize, Handle, Option<(Handle, usize)>)>,
    ) {
        self.events += 1;
        self.modified_nodes.insert((collapsed_prefix_node.forward(), prefix_len));
        let is_bubble = splitted_node_pairs.iter().all(|x| x.3.is_none());
        if is_bubble {
            self.bubbles += 1;
        }

        for (v, vlen, _, suffix) in splitted_node_pairs {
            // record transformation of node, even if none took place (which is the case if node v
            // equals the dedicated shared prefix node
            let mut replacement: Vec<(Handle, usize)> = Vec::new();
            replacement.push((collapsed_prefix_node, prefix_len));
            if let Some((u, ulen)) = suffix {
                replacement.push((*u, *ulen));
                self.modified_nodes.insert((u.forward(), *ulen));
            }

            // orient transformation
            // important notice:
            // - handle_graph::split_handle() works only in forward direction
            // - the first node of the split pair an will always be the node itself (again in
            //   forward direction)
            if v.is_reverse() {
                replacement.reverse();
                for r in replacement.iter_mut() {
                    r.0 = r.0.flip();
                }
            }
            log::debug!(
                "new replacement rule {}:{} -> {}",
                v.unpack_number(),
                vlen,
                replacement
                    .iter()
                    .map(|(r, rlen)| format!(
                        "{}{}:{}",
                        if r.is_reverse() { '<' } else { '>' },
                        r.unpack_number(),
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join("")
            );
            self.transform
                .insert((*v, *vlen), replacement.clone());
        }
    }

    fn expand(&self, v: Handle, vlen: usize) -> Vec<(Handle, usize)> {
        let mut res: Vec<(Handle, usize)> = Vec::new();

        if self.transform.contains_key(&(v.forward(), vlen)) {
            for (r, rlen) in self.transform.get(&(v.forward(), vlen)).unwrap() {
                // if identical node appears in its expansion sequence, don't expand...
                if (*r, *rlen) != (v, vlen) {
                    res.extend(self.expand(*r, *rlen));
                } else {
                    res.push((*r, *rlen));
                }
            }
            if v.is_reverse() {
                res.reverse();
                for x in res.iter_mut() {
                    x.0 = x.0.flip(); 
                }
            }
        } else {
            res.push((v, vlen));
        }

        res
    }

    fn deduplicate_transform(
        &mut self,
        node: Handle,
        node_len: usize,
        copies: &mut FxHashMap<(Handle, usize), Vec<Handle>>,
    ) {
        let mut queue = vec![(node.forward(), node_len)];

        while queue.len() > 0 {
            let (v, vlen) = queue.pop().unwrap();
            if self.transform.contains_key(&(v, vlen)) {
                let mut copy_of_v = v.clone();
                for (r, rlen) in self.transform.get_mut(&(v, vlen)).unwrap() {
                    let key = (r.forward(), rlen.clone());
                    if copies.contains_key(&key) {
                        // replace by a copy
                        let c = copies.get_mut(&key).unwrap().pop();
                        if c == None {
                            panic!("not enough copies available for node {}:{} to deduplicate transformation rule of {}:{}", key.0.unpack_number(), key.1, v.unpack_number(), vlen);
                        }
                        let r_new = c.unwrap();
                        log::debug!("replace {}:{} by {}:{} in de-duplication of transformation rule of {}:{}", r.unpack_number(), rlen, r_new.unpack_number(), rlen, v.unpack_number(), vlen);
                        *r = r_new;

                        // if copy is also key of transform table, then record new ID
                        if key == (v, vlen) {
                            copy_of_v = r.clone();
                        }
                    }
                    // if identical node appears in its expansion sequence, don't expand...
                    if (r.forward(), *rlen) != (copy_of_v.forward(), vlen) {
                        queue.push((r.forward(), *rlen));
                    }
                }

                // if copy is also key of transform table, then update key
                if copies.contains_key(&(v, vlen)) && copy_of_v.forward() != v {
                    let val = self.transform.remove(&(v, vlen)).unwrap();
                    self.transform.insert((copy_of_v.forward(), vlen.clone()), val);
                }
            }
        }
    }

    fn get_expanded_transformation(
        &self,
    ) -> FxHashMap<(Handle, usize), Vec<(Handle, usize)>> {
        let mut res: FxHashMap<(Handle, usize), Vec<(Handle, usize)>> =
            FxHashMap::default();
        res.reserve(self.transform.len());

        for (v, vlen) in self.transform.keys() {
            let expansion = self.expand(*v, *vlen);
            log::debug!(
                "deep-expansion of walk {} of node {}:{} into {}",
                self.transform
                    .get(&(*v, *vlen))
                    .unwrap()
                    .iter()
                    .map(|(r, rlen)| format!(
                        "{}{}:{}",
                        if r.is_reverse() { '<' } else { '>' },
                        r.unpack_number(),
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join(""),
                v.unpack_number(),
                vlen,
                expansion
                    .iter()
                    .map(|(r, rlen)| format!(
                        "{}{}:{}",
                        if r.is_reverse() { '<' } else { '>' },
                        r.unpack_number(),
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join("")
            );

            res.insert((*v, *vlen), expansion);
        }
        res
    }

    fn remove_selfloop_rules(&mut self) {
        let keys = self
            .transform
            .keys()
            .map(|(x, xlen)| (x.clone(), xlen.clone()))
            .collect::<Vec<(Handle, usize)>>();
        for (v, vlen) in keys {
            let rule = self.transform.get(&(v, vlen)).unwrap();
            if rule.len() == 1 && rule[0] == (v, vlen) {
                self.transform.remove(&(v, vlen));
            }
        }
    }

    fn decollapse(
        &mut self,
        graph: &mut HashGraph,
        mod_subg: &mut ModifiedSubGraph,
        nodes: FxHashSet<(Handle, usize)>,
    ) {
        let mut count: FxHashMap<(Handle, usize), usize> = FxHashMap::default();
        for (v, vlen) in nodes.iter() {
            let expansion = self.expand(*v, *vlen);

            for (u, ulen) in expansion.iter() {
                *count.entry((u.forward(), *ulen)).or_insert(0) += 1;
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
        let mut copies: FxHashMap<(Handle, usize), Vec<Handle>> = FxHashMap::default();
        for ((v, vlen), occ) in count.iter_mut() {
            // if a duplicated node is hit, create and record as many copies as needed to
            // de-duplicate it!
            if *occ > 1 {
                // yes, the duplicated node is a valid copy of its own!
                copies.entry((*v, *vlen)).or_insert(Vec::new()).push(*v);
            }
            // make some more copies
            while *occ > 1 {
                // create copy u of node v
                let u = graph.append_handle(&graph.sequence_vec(*v)[..]);
                log::debug!(
                    "creating duplicate {} of node {}",
                    u.unpack_number(),
                    v.unpack_number()
                );
                // copy incident edges of v onto u
                for w in graph.neighbors(*v, Direction::Left).collect::<Vec<Handle>>() {
                    log::debug!(
                        "creating duplicate edge <{}{}{}",
                        u.unpack_number(),
                        if w.is_reverse() { '<' } else { '>' },
                        w.unpack_number()
                    );
                    graph.create_edge(Edge(u.flip(), w.flip()));
                    mod_subg.record_added_edge(u.flip(), w.flip());
                }
                for w in graph
                    .neighbors(*v, Direction::Right)
                    .collect::<Vec<Handle>>()
                {
                    log::debug!(
                        "creating duplicate edge >{}{}{}",
                        u.unpack_number(),
                        if w.is_reverse() { '<' } else { '>' },
                        w.unpack_number()
                    );
                    graph.create_edge(Edge(u, w));
                    mod_subg.record_added_edge(u, w);
                }
                copies.get_mut(&(*v, *vlen)).unwrap().push(u);
                *occ -= 1
            }
        }

        // update transformation table
        for (v, vlen) in nodes.iter() {
            self.deduplicate_transform(*v, *vlen, &mut copies);
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

fn enumerate_walk_preserving_shared_affixes(
    graph: &HashGraph,
    mod_subg: &ModifiedSubGraph,
    v: Handle,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    let mut res: Vec<AffixSubgraph> = Vec::new();

    let mut branch: FxHashMap<(u8, Vec<Handle>), Vec<Handle>> = FxHashMap::default();
    // traverse multifurcation in the forward direction of the handle
    for u in graph.neighbors(v, Direction::Right) {
        if !mod_subg.node_deleted(&u) {
            // get parents of u
            let mut parents: Vec<Handle> = graph
                .neighbors(u, Direction::Left)
                .filter(|w| !mod_subg.node_deleted(&w))
                .collect();
            parents.sort();
            // insert child in walk-preserving data structure
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
    mod_subg: &mut ModifiedSubGraph,
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
    let mut splitted_node_pairs: Vec<(Handle, usize, Handle, Option<(Handle, usize)>)> =
        Vec::new();
    for (i, v) in shared_prefix_nodes.iter().enumerate() {
        let v_len = graph.node_len(*v);
        if v_len > prefix_len {
            // x corresponds to the shared prefix,
            let (x, u) = if v.is_reverse() {
                // it seems that rs-handlegraph is buggy when it comes to splitting nodes in
                // reverse direction
                let (u_rev, x_rev) = graph.split_handle(v.flip(), v_len - prefix_len);
                mod_subg.record_added(x_rev);
                (x_rev.flip(), u_rev.flip())
            } else {
                let (u, x) = graph.split_handle(*v, prefix_len);
                mod_subg.record_added(x);
                (u, x)
            };
            splitted_node_pairs.push((*v, v_len, x, Some((u, graph.node_len(u))),));
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
            splitted_node_pairs.push((*v, v_len, *v, None));
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
    let shared_prefix_node = shared_prefix_split.2;
    log::debug!(
        "node {}{} is dedicated shared prefix node",
        if shared_prefix_node.is_reverse() {
            '<'
        } else {
            '>'
        },
        shared_prefix_node.unpack_number()
    );

    for (_, _, u, maybe_v) in splitted_node_pairs.iter() {
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
                        mod_subg.record_added_edge(shared_prefix_node, *v);
                    }
                }
                None => {
                    // if node coincides with shared prefix (but is not the dedicated shared prefix
                    // node), then all outgoing edges of this node must be transferred to dedicated
                    // node
                    let outgoing_edges: Vec<Handle> = graph
                        .neighbors(*u, Direction::Right)
                        .filter(|v| !mod_subg.edge_deleted(&u, v))
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
                            mod_subg.record_added_edge(shared_prefix_node, x);
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
            mod_subg.record_deleted(*u);
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

fn find_and_collapse_walk_preserving_shared_affixes<W: Write>(
    graph: &mut HashGraph,
    out: &mut io::BufWriter<W>,
) -> (ModifiedSubGraph, CollapseEventTracker) {
    let mut mod_subg = ModifiedSubGraph::new();

    let mut event_tracker = CollapseEventTracker::new();

    let mut has_changed = true;
    while has_changed {
        has_changed = false;
        let mut queue: VecDeque<Handle> = VecDeque::new();
        queue.extend(graph.handles().chain(graph.handles().map(|v| v.flip())));
        while let Some(v) = queue.pop_front() {
            if !mod_subg.node_deleted(&v) {
                log::debug!(
                    "processing oriented node {}{}",
                    if v.is_reverse() { '<' } else { '>' },
                    v.unpack_number()
                );

                // process node in forward direction
                let affixes =
                    enumerate_walk_preserving_shared_affixes(graph, &mod_subg, v).unwrap();
                for affix in affixes.iter() {
                    has_changed |= true;
                    // in each iteration, the set of deleted nodes can change and affect the
                    // subsequent iteration, so we need to check the status the node every time
                    if affix
                        .shared_prefix_nodes
                        .iter()
                        .chain(affix.parents.iter())
                        .any(|u| mod_subg.node_deleted(u))
                    {
                        // push non-deleted parents back on queue
                        queue.extend(affix.parents.iter().filter(|u| !mod_subg.node_deleted(u)));
                    } else {
                        print(affix, out).unwrap();
                        if affix
                            .parents
                            .iter()
                            .chain(affix.shared_prefix_nodes.iter())
                            .any(|&u| {
                                event_tracker
                                    .modified_nodes
                                    .contains(&(u.forward(), graph.node_len(u)))
                            })
                        {
                            event_tracker.overlapping_events += 1
                        }
                        let shared_prefix_node =
                            collapse(graph, affix, &mut mod_subg, &mut event_tracker);
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
    (mod_subg, event_tracker)
}

fn transform_path(
    path: &Vec<(Handle, usize)>,
    transform: &FxHashMap<(Handle, usize), Vec<(Handle, usize)>>,
) -> Vec<Handle> {
    let mut res: Vec<Handle> = Vec::new();

    for (s, slen) in path.iter() {
        match transform.get(&(s.forward(), *slen)) {
            Some(us) => res.extend(
                if s.is_reverse() {
                    us.iter().rev().map(|(x, _)| x.flip()).collect::<Vec<Handle>>()
                } else {
                    us.iter().map(|(x, _)| *x).collect::<Vec<Handle>>()
                }),
            None => res.push(*s),
        }
    }

    res
}

fn unchop(
    graph: &mut HashGraph,
    mod_subg: &mut ModifiedSubGraph,
    nodes: FxHashSet<Handle>,
) -> FxHashMap<Vec<Handle>, Handle> {
    let mut res: FxHashMap<Vec<Handle>, Handle> = FxHashMap::default();

    // construction of 1:1 edges in two steps:
    //
    // 1. find 1-degree extremities, record edges that are part of it
    //
    let mut one_degree_ext: FxHashSet<Handle> = FxHashSet::default();
    let mut edge_set_loose: FxHashSet<(Handle, Handle)> = FxHashSet::default();

    for v in nodes.clone().into_iter().chain(nodes.clone().into_iter().map(|x| x.flip())) {
        let mut it = graph
            .neighbors(v, Direction::Right)
            .filter(|x| !mod_subg.node_deleted(x));
        if let Some(u) = it.next() {
            if let None = it.next() {
                one_degree_ext.insert(v);
                // yes, it's unusual encoding of edge: extremities are facing each other
                // but it make sense!
                let e = vec![(u, v.flip()), (v.flip(), u), (u.flip(), v), (v, u.flip())]
                    .into_iter()
                    .min()
                    .unwrap();
                edge_set_loose.insert(e);
            }
        }
    }

    // 2. iterate over edges, and filter those where both extremities are reported
    // identify paths of "chopped" nodes
    let mut edge_set_strict: Vec<(Handle, Handle)> = Vec::new();
    // extremity to edge mapping
    let mut ext_to_edge: FxHashMap<Handle, usize> = FxHashMap::default();
    for (u, v) in edge_set_loose.into_iter() {
        if one_degree_ext.contains(&u) && one_degree_ext.contains(&v) {
            let i = edge_set_strict.len();
            ext_to_edge.insert(u, i);
            ext_to_edge.insert(v, i);
            edge_set_strict.push((u, v));
        }
    }

    // union-find data structure to store class labels and sizes
    let mut classes: Vec<(usize, usize)> = (0..edge_set_strict.len())
        .zip(vec![0; edge_set_strict.len()])
        .collect();

    // find & merge
    for v in nodes.iter() {
        if ext_to_edge.contains_key(v) && ext_to_edge.contains_key(&v.flip()) {
            let i = ext_to_edge.get(v).unwrap();
            let j = ext_to_edge.get(&v.flip()).unwrap();

            let ir = root(&mut classes, *i);
            let jr = root(&mut classes, *j);
            if ir != jr {
                let is = classes[ir].1;
                let js = classes[jr].1;

                if is > js {
                    classes[jr] = (ir, 0);
                    classes[ir].1 += js;
                } else {
                    classes[ir] = (jr, 0);
                    classes[jr].1 += is;
                }
            }
        }
    }

    // collect chopped paths
    let mut clusters: Vec<Vec<usize>> = vec![Vec::new(); classes.len()];
    for i in 0..classes.len() {
        clusters[root(&mut classes, i)].push(i);
    }

    // unchop paths
    for p in clusters {
        if p.len() > 0 {
            // collect all node extremities that are part of the chopped path so that the end of
            // the path can be determined
            let mut path_ext: FxHashSet<Handle> = FxHashSet::default();
            for (u, v) in p.iter().map(|&x| edge_set_strict[x]) {
                path_ext.insert(u);
                path_ext.insert(v);
            }
            // now determine one end
            let mut v: Option<Handle> = None;
            let mut it = path_ext.iter();
            while v == None {
                let u = it.next().unwrap();
                if !path_ext.contains(&u.flip()) {
                    v = Some(*u);
                }
            }

            // guaranteed to work
            let mut v = v.unwrap();

            let mut ordered_path: Vec<Handle> = vec![v];
            ordered_path.reserve(p.len() + 1);
            let mut seq: Vec<u8> = Vec::new();
            seq.extend(graph.sequence_vec(v));

            while ext_to_edge.contains_key(&v) {
                let (u, w) = edge_set_strict[*ext_to_edge.get(&v).unwrap()];
                if u == v {
                    v = w.flip();
                } else {
                    v = u.flip();
                }
                seq.extend(graph.sequence_vec(v));
            }

            // create new unchopped node
            v = graph.append_handle(&seq[..]);
            mod_subg.record_added(v);

            // create new edges for left side of v
            for u in graph
                .neighbors(*ordered_path.first().unwrap(), Direction::Left)
                .filter(|x| !mod_subg.node_deleted(x)).collect::<Vec<Handle>>()
            {
                graph.create_edge(Edge(u, v));
                mod_subg.record_added_edge(u, v);
            }
            // create new edges for right side of v
            for u in graph
                .neighbors(*ordered_path.last().unwrap(), Direction::Right)
                .filter(|x| !mod_subg.node_deleted(x)).collect::<Vec<Handle>>()
            {
                graph.create_edge(Edge(v, u));
                mod_subg.record_added_edge(v, u);
            }
            // delete chopped path
            for u in ordered_path.iter() {
                mod_subg.record_deleted(*u);
            }

            // record graph modification
            res.insert(ordered_path, v);
        }
    }

    res
}

fn root(classes: &mut Vec<(usize, usize)>, i: usize) -> usize {
    // get root tree of union-find data structure, compress path on the way up

    // find root
    let mut r = i;

    let mut path: Vec<usize> = Vec::new();
    let mut class_size = 0;
    while classes[r].0 != r {
        class_size += classes[r].1;
        path.push(r);
        r = classes[r].0;
    }
    if r != i {
        classes[r].1 += class_size;
        // re-wire and set size of class for non-root members to zero
        for u in path {
            classes[u] = (r, 0);
        }
    }
    r
}

//fn consolidate_transform(graph: &HashGraph, mod_subg: &ModifiedSubGraph, transform: &
//    FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>, unchopped: FxHashMap<Vec<Handle>>, ) -> FxHashMap<Vec<(usize, Direction, usize)>, Vec<(usize, Direction, usize)>> {
//
//    let collapsed_paths : FxHashMap<Vec<Handle>, (usize, Direction, usize)> = FxHashMap::default();
//
//    for p in transform.values_mut() {
//        let new_p : Vec<(usize, Direction, usize)> = Vec::default();
//        let mut has_changed = false;
//        let it = p.iter();
//        while it.has_next() {
//            let (vid, vo, vl) = it.next();
//            let v = Handle::pack(vid, vo);
//            if corrected_degree(graph, mod_subg, v) == 1 {
//                // find maximal compressable path
//                let cur_p Vec<Handle> = vec![v];
//                while it.has_next() && corrected_degree(graph, mod_subg, cur_p[-1]) == 1 {
//                    let u = it.filter(|x| !mod_subg.node_deleted(x)).next().unwrap();
//                    cur_p.push(u);
//                }
//                if collapsed_paths.contains_key(cur_p) {
//                    new_p.push(collapsed_paths.get(cur_p).unwrap());
//                } else {
//                    let cur_p_rev = cur_p.iter().reverse().map(|x| x.flip()).collect();
//                    if collapsed_paths.contains_key(cur_p_rev) {
//                        let (cid, co, cl) = collapsed_paths.get(cur_p_rev).unwrap();
//                        new_p.push((cid, if co == Direction::Left { Direction::Right } else { Direction::Right }, cl));
//                    } else {
//                        let seq: Vec<u8> = cur_p.map(|u| graph.sequence_vec(u)).collect()[..]).concat();
//                        let u = graph.append_handle(seq);
//                        new_p.push((u.unpack_number(), if u.is_reverse() { Direction::Left } else { Direction::Right }, seq.len()));
//                    }
//                }
//                has_changed = true;
//            } else {
//                new_p.push((vid, vo, vl));
//            }
//        }
//        if has_changed {
//            p.clear();
//            p.extend(new_p);
//        }
//    }
//}

fn corrected_degree(graph: &HashGraph, mod_subg: &ModifiedSubGraph, v: Handle) -> usize {
    let mut d = 0;

    for u in graph.neighbors(v, Direction::Right) {
        if !mod_subg.edge_deleted(&u, &v) {
            d += 1
        }
    }
    d
}

fn print_active_subgraph<W: io::Write>(
    graph: &HashGraph,
    mod_subg: &ModifiedSubGraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    writeln!(out, "H\tVN:Z:1.0")?;
    for v in graph.handles() {
        if !mod_subg.node_deleted(&v) {
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
        if !mod_subg.edge_deleted(&u, &v) {
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
    transform: &FxHashMap<(Handle, usize), Vec<(Handle, usize)>>,
) {
    for ((v, vlen), path) in transform.iter() {
        let path_len: usize = path.iter().map(|x| x.1).sum();
        if *vlen != path_len {
            panic!(
                "length of walk {} does not sum up to that of its replacing node of {}:{}",
                path.iter()
                    .map(|(r, rlen)| format!(
                        "{}{}:{}",
                        if r.is_reverse() { '<' } else { '>' },
                        r.unpack_number(),
                        rlen
                    ))
                    .collect::<Vec<String>>()
                    .join(""),
                v.unpack_number(),
                vlen
            );
        }

        if old_graph.has_node(v.id()) && old_graph.node_len(*v) == *vlen {
            let old_seq = old_graph.sequence_vec(*v);
            let new_seq = spell_walk(new_graph, path);
            if old_seq != new_seq {
                panic!(
                    "node {} in old graph spells sequence {}, but walk {} in new graph spell sequence {}", 
                    v.unpack_number(),
                    String::from_utf8(old_seq).unwrap(),
                    path.iter()
                        .map(|(r, _)| format!(
                                "{}{}",
                                if r.is_reverse() { '<' } else { '>' },
                        r.unpack_number(),))
                        .collect::<Vec<String>>()
                        .join(""), 
                    String::from_utf8(new_seq).unwrap()
                    );
            }
        }
    }
}

fn print_transformations<W: Write>(
    transform: &FxHashMap<(Handle, usize), Vec<(Handle, usize)>>,
    orig_node_lens: &FxHashMap<Handle, usize>,
    out: &mut io::BufWriter<W>,
) -> Result<(), io::Error> {
    writeln!(
        out,
        "{}",
        ["original_node", "transformed_walk", "bp_length"].join("\t")
    )?;

    for ((v, vlen), path) in transform.iter() {
        if match orig_node_lens.get(v) {
            Some(l) => l == vlen,
            _ => false,
        } && (path.len() > 1 || *v != path[0].0)
        {
            writeln!(
                out,
                "{}\t{}\t{}",
                v.unpack_number(),
                path.iter()
                    .map(|(r, _)| format!(
                        "{}{}",
                        if r.is_reverse() { '<' } else { '>' },
                        r.unpack_number(),
                    ))
                    .collect::<Vec<String>>()
                    .join(""),
                vlen
            )?;
        }
    }
    Ok(())
}

fn spell_walk(graph: &HashGraph, walk: &Vec<(Handle, usize)>) -> Vec<u8> {
    let mut res: Vec<u8> = Vec::new();

    let mut prev_v: Option<Handle> = None;
    for (i, (v, _)) in walk.iter().enumerate() {
        if i >= 1 && !graph.has_edge(prev_v.unwrap(), *v) {
            panic!("graph does not have edge {:?}-{:?}", &walk[i - 1], &walk[i]);
        }
        res.extend(graph.sequence_vec(*v));
        prev_v = Some(*v);
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
    orig_node_lens: &FxHashMap<Handle, usize>,
    transform: &FxHashMap<(Handle, usize), Vec<(Handle, usize)>>,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    for path in gfa.paths.iter() {
        log::debug!("transforming path {}", str::from_utf8(&path.path_name)?);
        let tpath = transform_path(
            &path
                .iter()
                .map(|(sid, o)| {
                    (
                        Handle::pack(sid, o == Orientation::Backward),
                        *orig_node_lens.get(&Handle::pack(sid, false)).unwrap(),
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
                .map(|v| format!( "{}{}", v.unpack_number(),
                    if v.is_reverse() { '-' } else { '+' }
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
    transform: &FxHashMap<(Handle, usize), Vec<(Handle, usize)>>,
    orig_node_lens: &FxHashMap<Handle, usize>,
    //    mod_subg: &ModifiedSubGraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), io::Error> {
    let reader = Csv::from_reader(&mut data)
        .delimiter(b'\t')
        .flexible(true)
        .has_header(false);

    for row in reader.into_iter() {
        let row = row.unwrap();
        let mut row_it = row.bytes_columns();

        if &[b'W'] == row_it.next().unwrap() {
            let sample_id = str::from_utf8(row_it.next().unwrap()).unwrap();
            let hap_idx = str::from_utf8(row_it.next().unwrap()).unwrap();
            let seq_id = str::from_utf8(row_it.next().unwrap()).unwrap();
            let seq_start = str::from_utf8(row_it.next().unwrap()).unwrap();
            let seq_end = str::from_utf8(row_it.next().unwrap()).unwrap();
            let walk_ident = format!(
                "{}#{}#{}:{}-{}",
                sample_id, hap_idx, seq_id, seq_start, seq_end
            );
            log::debug!("transforming walk {}", walk_ident);

            let walk_data = row_it.next().unwrap();
            let mut walk: Vec<(Handle, usize)> = Vec::new();

            let mut cur_el: Vec<u8> = Vec::new();
            for c in walk_data {
                if (c == &b'>' || c == &b'<') && !cur_el.is_empty() {
                    let sid = usize::from_str(str::from_utf8(&cur_el[1..]).unwrap()).unwrap();
                    let v = Handle::pack(sid, cur_el[0] == b'<');
                    walk.push((v, *orig_node_lens.get(&v.forward()).unwrap()));
                    cur_el.clear();
                }
                cur_el.push(*c);
            }

            if !cur_el.is_empty() {
                let sid = usize::from_str(str::from_utf8(&cur_el[1..]).unwrap()).unwrap();
                let v = Handle::pack(sid, cur_el[0] == b'<');
                walk.push((v,
                        *orig_node_lens.get(&v.forward()).unwrap()));
            }

            let tpath = transform_path(&walk, &transform);
            //            check_path(graph, mod_subg, &tpath);
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
                    .map(|v| format!(
                        "{}{}",
                        if v.is_reverse() { '<' } else { '>' },
                        v.unpack_number() 
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

    // check if regex of no_collapse_path is valid
    if !params.no_collapse_path.trim().is_empty() && Regex::new(&params.no_collapse_path).is_err() {
        panic!(
            "Supplied string \"{}\" is not a valid regular expression",
            params.no_collapse_path
        );
    }

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
    let mut node_lens: FxHashMap<Handle, usize> = FxHashMap::default();
    node_lens.reserve(graph.node_count());
    for v in graph.handles() {
        node_lens.insert(v, graph.node_len(v));
    }

    let mut dont_collapse_nodes: FxHashSet<(Handle, usize)> = FxHashSet::default();

    if !params.no_collapse_path.trim().is_empty() {
        let re = Regex::new(&params.no_collapse_path).unwrap();
        for path_id in graph.paths.keys() {
            let path_name_vec = graph.get_path_name_vec(*path_id).unwrap();
            let path_name = str::from_utf8(&path_name_vec[..]).unwrap();
            if re.is_match(&path_name) {
                let path = graph.get_path(path_id).unwrap();
                dont_collapse_nodes.extend(path.nodes.iter().map(|&x| {
                    (x.forward(), *node_lens.get(&x.forward()).unwrap())
                }));

                log::info!(
                    "flagging nodes of path {} as non-collapsing, total number is now at {}",
                    path_name,
                    dont_collapse_nodes.len()
                );
            }
        }
    }

    //
    // REMOVING PATHS FROM GRAPH -- they SUBSTANTIALLY slow down graph editing
    //
    graph.paths.clear();

    log::info!("identifying walk-preserving shared prefixes");
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

    let (mut mod_subg, mut event_tracker) =
        find_and_collapse_walk_preserving_shared_affixes(&mut graph, &mut out);

    // remove unneccessary transformations that lead to infinite loops...
    event_tracker.remove_selfloop_rules();

    if dont_collapse_nodes.len() > 0 {
        log::info!("de-collapse no-collapse handles and update transformation table");
        event_tracker.decollapse(&mut graph, &mut mod_subg, dont_collapse_nodes);
    }

    log::info!("expand transformation table");
    let transform = event_tracker.get_expanded_transformation();

    log::info!("unchopping modified paths");

    let mut involved_nodes: FxHashSet<Handle> = FxHashSet::default();
    for p in transform.values() {
        involved_nodes.extend(p.iter().map(|(vid, _,)| Handle::pack(*vid, false)));
        involved_nodes.extend(
            graph
                .neighbors(p.first().unwrap().0, Direction::Left)
                .filter(|u| !mod_subg.node_deleted(&u))
                .collect::<Vec<Handle>>(),
        );
        involved_nodes.extend(
            graph
                .neighbors(p.last().unwrap().0, Direction::Right)
                .filter(|u| !mod_subg.node_deleted(&u))
                .collect::<Vec<Handle>>(),
        );
    }

    unchop(&mut graph, &mut mod_subg, involved_nodes);

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
        if let Err(e) = print_active_subgraph(&graph, &mod_subg, &mut graph_out) {
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
