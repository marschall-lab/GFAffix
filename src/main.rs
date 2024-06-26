/* standard use */
use std::collections::{HashSet, VecDeque};
use std::error::Error;
use std::fs;
use std::io;
use std::io::prelude::*;
use std::iter::{repeat, FromIterator};
use std::str::{self, FromStr};

/* crate use */
use clap::Parser;
use gfa::{
    gfa::{orientation::Orientation, GFA},
    optfields::OptFields,
    parser::GFAParser,
};
use handlegraph::{
    handle::{Direction, Edge, Handle},
    handlegraph::*,
    hashgraph::HashGraph,
    mutablehandlegraph::{AdditiveHandleGraph, MutableHandles},
    pathhandlegraph::GraphPathNames,
};
use rayon::prelude::*;
use regex::Regex;
use rustc_hash::{FxHashMap, FxHashSet};
use std::sync::{Arc, Mutex};

/* mod declaration */
mod collapse_event_tracker;
use collapse_event_tracker::*;
mod affix_sub_graph;
use affix_sub_graph::*;
mod deleted_sub_graph;
use deleted_sub_graph::*;
mod walk_transform;
use walk_transform::*;
mod decomposition;
use decomposition::*;

const EXPLORE_NEIGHBORHOOD: usize = 2;

#[derive(Parser, Debug)]
#[clap(
    version = "0.1.5b",
    author = "Daniel Doerr <daniel.doerr@hhu.de>",
    about = "Discover and collapse walk-preserving shared affixes of a given variation graph.\n
    - Do you want log output? Call program with 'RUST_LOG=info gfaffix ...'
    - Log output not informative enough? Try 'RUST_LOG=debug gfaffix ...'"
)]
pub struct Command {
    #[clap(index = 1, help = "graph in GFA1 format", required = true)]
    pub graph: String,

    #[clap(
        short = 'o',
        long = "output_refined",
        help = "Write refined graph in GFA1 format to supplied file",
        default_value = " "
    )]
    pub refined_graph_out: String,

    #[clap(
        short = 't',
        long = "output_transformation",
        help = "Report original nodes and their corresponding walks in refined graph to supplied file",
        default_value = " "
    )]
    pub transformation_out: String,

    #[clap(
        short = 'c',
        long = "check_transformation",
        help = "Verifies that the transformed parts of the graphs spell out the identical sequence as in the original graph"
    )]
    pub check_transformation: bool,

    #[clap(
        short = 'x',
        long = "dont_collapse",
        help = "Do not collapse nodes on a given paths (\"P\" lines) that match given regular expression",
        default_value = " "
    )]
    pub no_collapse_path: String,

    #[clap(
        short = 'p',
        long,
        help = "Run in parallel on N threads",
        default_value = "1"
    )]
    threads: usize,
}

pub fn v2str(v: &Handle) -> String {
    format!(
        "{}{}",
        if v.is_reverse() { '<' } else { '>' },
        v.unpack_number()
    )
}

pub fn v2tuple(graph: &HashGraph, v: &Handle) -> (usize, Direction, usize) {
    (
        v.unpack_number() as usize,
        if v.is_reverse() {
            Direction::Left
        } else {
            Direction::Right
        },
        graph.node_len(*v),
    )
}

fn enumerate_branch(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    v: &Handle,
) -> FxHashMap<(u8, Vec<Handle>), VecDeque<Handle>> {
    let mut branch: FxHashMap<(u8, Vec<Handle>), VecDeque<Handle>> = FxHashMap::default();

    // traverse multifurcation in the forward direction of the handle
    for u in graph.neighbors(*v, Direction::Right) {
        if !del_subg.edge_deleted(v, &u) {
            // get parents of u
            let mut parents: Vec<Handle> = graph
                .neighbors(u, Direction::Left)
                .filter(|w| !del_subg.edge_deleted(w, &u))
                .collect();

            parents.par_sort();

            // insert child in walk-preserving data structure
            let mut c = graph.base(u, 0).unwrap();
            // make all letters uppercase
            if c >= 90 {
                c -= 32
            }
            let children = branch.entry((c, parents)).or_insert_with(VecDeque::new);

            // Sort handles with shared prefix so that reversed ones come first! This is important
            // for the case that two shared prefixes correspond to the same node, one in forward,
            // and one in backward dirction (e.g. >1209, <1209 share prefix 'C'). In those cases,
            // the code that splits handles only works iff the backward oriented handle is split
            // first (e.g., <1209 is split into <329203 and <1209) and then the forward oriented
            // handle (e.g., truncated handle >1209 is split into >1209 and 329204), Subsequently,
            // either >1209 or >329203 is deleted, with the other being advanced as dedicated
            // shared prefix node.

            if u.is_reverse() {
                children.push_front(u);
            } else {
                children.push_back(u);
            }
        }
    }

    branch
}

fn enumerate_walk_preserving_shared_affixes(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    v: Handle,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    let mut res: Vec<AffixSubgraph> = Vec::new();

    // we do not allow that the same child is modified in the same iteration by two different
    // collapses as this will lead to an erroneous reduction; this can happen if both prefix and
    // suffix of a child share affixes from two different subsets; in order to prevent this, we
    // maintain a "visited" list of children. If a child appears later in another identified shared
    // affix, the instance will be simply ignored (and found again at some later iteration, which
    // is then fine).
    let mut visited_children: FxHashSet<Handle> = FxHashSet::default();
    let branch = enumerate_branch(graph, del_subg, &v);

    for ((c, parents), children) in branch.into_iter() {
        if children.len() > 1 && (c == b'A' || c == b'C' || c == b'G' || c == b'T') {
            let mut children_vec: Vec<Handle> = children.into();
            let mut prefix = get_shared_prefix(&children_vec, graph)?;
            log::debug!(
                "identified shared affix {} between nodes {} originating from parent(s) {}",
                if prefix.len() > 10 {
                    prefix[..10].to_string() + "..."
                } else {
                    prefix.clone()
                },
                children_vec
                    .iter()
                    .map(v2str)
                    .collect::<Vec<String>>()
                    .join(","),
                parents.iter().map(v2str).collect::<Vec<String>>().join(",")
            );
            let mut multiplicity: FxHashMap<Handle, usize> = FxHashMap::default();
            children_vec.iter().for_each(|v| {
                multiplicity
                    .entry(v.forward())
                    .and_modify(|m| *m += 1)
                    .or_insert(1);
            });

            multiplicity.into_iter().for_each(|(v, m)| {
                if m > 1 {
                    let l = graph.node_len(v);
                    if prefix.len() == l {
                        // found palindrome! Let's remove the forward version of it
                        log::info!("node {} is a palindrome", v.unpack_number());
                        // remember that children_vec is ordered, i.e., reverse followed by forward
                        // nodes? So if the palindromic forward node is removed and replaced by the
                        // last element (that's what swap_remove does), this order is still
                        // maintained
                        children_vec
                            .swap_remove(children_vec.iter().position(|&u| u == v).unwrap());
                    } else if prefix.len() > l/2 {
                        log::info!("prefix and suffix of node {} (length {}) share an overlapping match (overlap: {}bp), clipping overlap", 
                            v.unpack_number(),
                            l,
                            prefix.len() * 2 - l);
                        prefix.truncate(l/2);
                    }
                }
            });
            if children_vec.len() > 1 {
                if children_vec
                    .iter()
                    .all(|x| !visited_children.contains(&x.forward()))
                {
                    // add children to the list of previously visited children
                    visited_children.extend(children_vec.iter().map(|x| x.forward()));
                    // we are removing children if nodes are palindromes, so if only one node is left,
                    // don't do anything
                    res.push(AffixSubgraph {
                        sequence: prefix,
                        parents: parents,
                        shared_prefix_nodes: children_vec,
                    });
                } else {
                    log::debug!("skip shared affix because it shares children with a previous affix (will be collapsed next time)");
                }
            }
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
    // let's commence the collapse!
    let prefix_len = shared_prefix.sequence.len();

    // update graph in two passes:
    //  1. split handle into shared prefix and distinct suffix and appoint dedicated shared
    //  prefix node
    //  2. update deleted edge set, reassign outgoing edges of "empty" nodes to dedicated shared
    //     prefix node
    // each element in splitted_node_pairs is of the form:
    //  1. node ID of original handle
    //  2. direction of original handle
    //  3. length of original handle
    //  4-5. splitted handle (IMPORTANT: that's generally not equivalent with the replacement
    //  handles!)
    let mut splitted_node_pairs: Vec<(usize, Direction, usize, Handle, Option<(Handle, usize)>)> =
        Vec::new();

    let mut shared_prefix_node: Option<Handle> = None;

    // edges need to be stored only for the case where the set contains a don't-collapse-node and
    // any (incl. the d-c-n) is blunt, i.e., has the same length as the shared prefix. All other
    // "non-blunt" edges can be trivially restored, it's just when blunt nodes collapse that the
    // original incident edges need to be restored. In other words, and *THIS IS IMPORTANT*, the
    // retained edge set is not complete (it does not contain the non-blunt edges), but only covers
    // the essential part of the graph adjacencies that must be restored

    let mut has_blunt_nodes = false;
    let mut original_edges: Vec<((usize, Direction, usize), Vec<(usize, Direction, usize)>)> =
        Vec::new();
    let mut n_dont_collapse_nodes = 0;

    for v in shared_prefix.shared_prefix_nodes.iter() {
        let v_len = graph.node_len(*v);
        let node_id = v.unpack_number() as usize;
        let node_orient = if v.is_reverse() {
            Direction::Left
        } else {
            Direction::Right
        };

        // count don't collapse nodes
        let isDontCollapse = event_tracker
            .dont_collapse_nodes
            .contains(&(node_id, v_len));
        if isDontCollapse {
            n_dont_collapse_nodes += 1;
        }
        if v_len > prefix_len {
            // x corresponds to the shared prefix,
            let (x, u) = if v.is_reverse() {
                // apparently, rs-handlegraph does not allow splitting nodes in reverse direction
                let (u_rev, x_rev) = graph.split_handle(v.flip(), v_len - prefix_len);
                (x_rev.flip(), u_rev.flip())
            } else {
                graph.split_handle(*v, prefix_len)
            };
            // update dedicated shared prefix node if none has been assigned yet
            log::debug!(
                "splitting node {} into prefix {} and suffix {}",
                v2str(v),
                v2str(&x),
                v2str(&u)
            );
            //            if isDontCollapse {
            //                log::debug!(
            //                    "original node is a don't collapse node, adding new nodes {} and {} to don't collapse collection",
            //                    v2str(&x),
            //                    v2str(&u)
            //                );
            //                let (xid, _, xlen) = v2tuple(graph, &x);
            //                event_tracker.dont_collapse_nodes.insert((xid, xlen));
            //                let (uid, _, ulen) = v2tuple(graph, &u);
            //                event_tracker.dont_collapse_nodes.insert((uid, ulen));
            //            }

            splitted_node_pairs.push((
                node_id,
                node_orient,
                v_len,
                x,
                Some((u, graph.node_len(u))),
            ));

            match shared_prefix_node {
                None => {
                    log::debug!("node {} is dedicated shared prefix node", v2str(&x));
                    shared_prefix_node = Some(x);
                }
                Some(w) => {
                    // make all suffixes adjacent to shared suffix node
                    if !graph.has_edge(w, u) {
                        graph.create_edge(Edge::edge_handle(w, u));
                        log::debug!("create edge {}{}", v2str(&w), v2str(&u));
                        // mark redundant node as deleted
                        log::debug!("flag {} as deleted", v2str(&x));
                        del_subg.add_node(x);
                    }
                }
            };

            // to properly disentagle decollapsed non-collapsible nodes in presence of blunt nodes,
            // non-blunt nodes (suffix is non-empty) need to be recorded
            let spn = shared_prefix_node.unwrap();
            original_edges.push((v2tuple(graph, &spn), vec![v2tuple(graph, &u)]));
        } else {
            splitted_node_pairs.push((node_id, node_orient, v_len, *v, None));
            log::debug!(
                "node {} matches prefix {}",
                v2str(v),
                if prefix_len > 10 {
                    shared_prefix.sequence[..10].to_string() + "..."
                } else {
                    shared_prefix.sequence.clone()
                }
            );
            has_blunt_nodes = true;
            original_edges.push((
                (node_id, node_orient, v_len),
                graph
                    .neighbors(*v, Direction::Right)
                    .filter(|u| !del_subg.edge_deleted(v, u))
                    .map(|u| v2tuple(graph, &u))
                    .collect(),
            ));

            match shared_prefix_node {
                None => {
                    log::debug!("node {} is dedicated shared prefix node", v2str(v));
                    shared_prefix_node = Some(*v);
                }
                Some(w) => {
                    // if node coincides with shared prefix (but is not the dedicated shared prefix
                    // node), then all outgoing edges of this node must be transferred to dedicated
                    // node
                    let outgoing_edges: Vec<Handle> = graph
                        .neighbors(*v, Direction::Right)
                        .filter(|u| !del_subg.edge_deleted(v, u))
                        .collect();
                    for mut x in outgoing_edges {
                        if &x == v {
                            x = w;
                        } else if x == v.flip() {
                            x = w.flip()
                        }
                        if !graph.has_edge(w, x) {
                            graph.create_edge(Edge::edge_handle(w, x));
                            log::debug!("create edge {}{}", v2str(&w), v2str(&x));
                        }
                    }
                    // mark redundant node as deleted
                    log::debug!("flag {} as deleted", v2str(v));
                    del_subg.add_node(*v);
                }
            };
        }
    }

    if n_dont_collapse_nodes >= 2 {
        //
        // The neighborhood of nodes that are not supposed to be collapsed needs to be saved, so
        // that we can restore them later on. You might ask yourself--then why do we collapse those
        // nodes in the first place? Well, turns out that there are situations where the
        // de-collapsed graph is more condensed than a not-at-all-collapsed graph, because of
        // subsequent collapses of decollapsible nodes.
        //
        // This neighborhood needs only be recovered if blunt nodes are involved
        if !has_blunt_nodes {
            original_edges.clear();
        }
        event_tracker.retain_dont_collapse_edges(original_edges);
    }

    let spn = shared_prefix_node.unwrap();
    event_tracker.report(spn, prefix_len, &splitted_node_pairs);
    spn
}

fn get_shared_prefix(
    nodes: &[Handle],
    graph: &HashGraph,
) -> Result<String, std::string::FromUtf8Error> {
    let mut seq: Vec<u8> = Vec::new();

    let sequences: Vec<Vec<u8>> = nodes.par_iter().map(|v| graph.sequence_vec(*v)).collect();

    let mut i = 0;
    while sequences[0].len() > i {
        let c: u8 = sequences[0][i];

        if sequences.iter().any(|other| {
            other.len() <= i
                || !matches!(
                    (other[i], c),
                    (b'A', b'A')
                        | (b'A', b'a')
                        | (b'a', b'A')
                        | (b'a', b'a')
                        | (b'C', b'C')
                        | (b'C', b'c')
                        | (b'c', b'C')
                        | (b'c', b'c')
                        | (b'G', b'G')
                        | (b'G', b'g')
                        | (b'g', b'G')
                        | (b'g', b'g')
                        | (b'T', b'T')
                        | (b'T', b't')
                        | (b't', b'T')
                        | (b't', b't')
                )
        }) {
            break;
        }
        seq.push(c);
        i += 1;
    }

    String::from_utf8(seq)
}

fn find_walk_preserving_shared_affixes(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    nodes: Vec<Handle>,
) -> Vec<AffixSubgraph> {
    nodes
        .par_iter()
        .filter_map(|v| {
            if !del_subg.node_deleted(v) {
                Some(enumerate_walk_preserving_shared_affixes(graph, &del_subg, *v).unwrap())
            } else {
                None
            }
        })
        .flatten()
        .collect()
}

fn find_affected_nodes(graph: &HashGraph, del_subg: &DeletedSubGraph, v: Handle) -> Vec<Handle> {
    let mut queue: Vec<(usize, Handle)> = vec![(0, v)];

    let mut visited = FxHashSet::default();

    let mut res = Vec::new();

    while !queue.is_empty() {
        let (d, v) = queue.pop().unwrap();
        if !del_subg.node_deleted(&v) && !visited.contains(&v.forward()) {
            visited.insert(v.forward());
            res.push(v);
            res.push(v.flip());
            if d < EXPLORE_NEIGHBORHOOD {
                queue.extend(
                    graph
                        .neighbors(v, Direction::Right)
                        .chain(graph.neighbors(v, Direction::Left))
                        .filter_map(|u| {
                            if !visited.contains(&u.forward()) {
                                Some((d + 1, u.forward()))
                            } else {
                                None
                            }
                        }),
                );
            }
        }
    }

    res
}

fn find_collapsible_blunt_end_pair(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    v: Handle,
) -> Option<Handle> {
    if del_subg.node_deleted(&v) || graph.degree(v, Direction::Left) > 0 {
        None
    } else {
        let l = graph.node_len(v);
        graph
            .neighbors(v, Direction::Right)
            .filter_map(|u| {
                if del_subg.node_deleted(&u) {
                    None
                } else {
                    graph
                        .neighbors(u, Direction::Left)
                        .filter_map(|w| {
                            if del_subg.node_deleted(&w)
                                || w == v
                                || get_shared_prefix(&[w.flip(), v.flip()], graph)
                                    .unwrap()
                                    .len()
                                    != l
                                || !HashSet::<Handle>::from_iter(
                                    graph.neighbors(v, Direction::Right),
                                )
                                .is_subset(&HashSet::from_iter(
                                    graph.neighbors(w, Direction::Right),
                                ))
                            {
                                None
                            } else {
                                log::info!(
                                    "found collapsible blunt end pair {}, {}",
                                    v2str(&v),
                                    v2str(&w)
                                );
                                Some(w)
                            }
                        })
                        .next()
                }
            })
            .next()
    }
}

fn find_and_collapse_blunt_ends(
    graph: &mut HashGraph,
    del_subg: &mut DeletedSubGraph,
    event_tracker: &mut CollapseEventTracker,
) {
    let mut queue: Vec<Handle> = graph
        .handles()
        .chain(graph.handles().map(|v| v.flip()))
        .collect();

    while !queue.is_empty() {
        let collapsible_blunts: Vec<(Handle, Handle)> = queue
            .par_iter()
            .filter_map(|&v| find_collapsible_blunt_end_pair(graph, del_subg, v).map(|u| (v, u)))
            .collect();

        let mut modified_nodes: FxHashSet<Handle> = FxHashSet::default();
        let mut new_queue: Vec<Handle> = Vec::new();
        for (v, u) in collapsible_blunts {
            if modified_nodes.contains(&v.forward()) || modified_nodes.contains(&u.forward()) {
                // we only need to re-assess the blunt end
                new_queue.push(v);
            } else {
                // remove *one* character, because VG assumes that each chromosome starts with a
                // left-degree 0 node
                let prefix = String::from_utf8({
                    let mut x = graph.sequence_vec(v.flip());
                    x.pop();
                    x
                })
                .unwrap();
                if !prefix.is_empty() {
                    collapse(
                        graph,
                        &AffixSubgraph {
                            sequence: prefix,
                            parents: graph
                                .neighbors(v, Direction::Right)
                                .map(|v| v.flip())
                                .collect(),
                            shared_prefix_nodes: vec![v.flip(), u.flip()],
                        },
                        del_subg,
                        event_tracker,
                    );
                    modified_nodes.insert(v.forward());
                    modified_nodes.insert(u.forward());
                }
            }
        }
        queue = new_queue;
    }
}

fn find_and_collapse_walk_preserving_shared_affixes<'a>(
    graph: &mut HashGraph,
    dont_collapse_nodes: &'a FxHashSet<(usize, usize)>,
) -> (
    Vec<AffixSubgraph>,
    DeletedSubGraph,
    CollapseEventTracker<'a>,
) {
    let mut affixes = Vec::new();
    let mut del_subg = DeletedSubGraph::new();

    let mut event_tracker = CollapseEventTracker::new(dont_collapse_nodes);

    let mut has_changed = true;
    while has_changed {
        has_changed = false;
        let mut queue: Vec<Handle> = graph
            .handles()
            .chain(graph.handles().map(|v| v.flip()))
            .collect();
        while !queue.is_empty() {
            let cur_affixes = find_walk_preserving_shared_affixes(graph, &del_subg, queue);
            queue = Vec::new();
            let mut cur_modified_nodes = FxHashSet::default();
            for affix in cur_affixes.iter() {
                // in each iteration, the set of deleted nodes can change and affect the
                // subsequent iteration, so we need to check the status the node every time
                if affix
                    .shared_prefix_nodes
                    .iter()
                    .chain(affix.parents.iter())
                    .any(|u| del_subg.node_deleted(u) || cur_modified_nodes.contains(&u.forward()))
                {
                    // push non-deleted parents back on queue
                    queue.extend(affix.parents.iter().filter_map(|u| {
                        if !del_subg.node_deleted(u) {
                            Some(u.flip())
                        } else {
                            None
                        }
                    }));
                } else {
                    has_changed |= true;
                    affixes.push(affix.clone());
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
                    cur_modified_nodes.extend(affix.parents.iter().filter_map(|u| {
                        if !del_subg.node_deleted(u) {
                            Some(u.forward())
                        } else {
                            None
                        }
                    }));
                    cur_modified_nodes.extend(affix.shared_prefix_nodes.iter().filter_map(|u| {
                        if !del_subg.node_deleted(u) {
                            Some(u.forward())
                        } else {
                            None
                        }
                    }));
                    queue.extend(find_affected_nodes(graph, &del_subg, shared_prefix_node));
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
    (affixes, del_subg, event_tracker)
}

fn merge_graphs(
    component: Vec<HashGraph>,
    endpoints: HashGraph,
    del_subg: &DeletedSubGraph,
) -> HashGraph {
    let mut res = endpoints;

    for g in component {
        for v in g.handles() {
            if !del_subg.node_deleted(&v) && !res.has_node(v) {
                res.create_handle(&g.sequence_vec(v)[..], v.id());
            }
        }
        for e in g.edges() {
            if !del_subg.edge_deleted(&e.0, &e.1) {
                assert!(!res.has_edge(e.0, e.1), "assumed edges are disjoint");
                res.create_edge(e);
            }
        }
    }

    res
}

fn transform_node(
    vid: usize,
    orient: Orientation,
    v_len: usize,
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
) -> Vec<(usize, Direction)> {
    match transform.get(&(vid, v_len)) {
        Some(us) => match orient {
            Orientation::Forward => us.iter().map(|(x, y, _)| (*x, *y)).collect(),
            Orientation::Backward => us
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
                .collect(),
        },
        None => vec![(
            vid,
            match orient {
                Orientation::Forward => Direction::Right,
                Orientation::Backward => Direction::Left,
            },
        )],
    }
}

fn print_active_subgraph<W: io::Write>(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
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
    del_subg: &DeletedSubGraph,
) {
    transform.par_iter().for_each(|((vid, vlen), path)| {
        let path_len: usize = path.iter().map(|x| x.2).sum();
        if *vlen != path_len {
            panic!(
                "length of walk {} does not sum up to that of its replacing node of {}:{}",
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

        if path.len() > 1 {
            for i in 0..(path.len() - 1) {
                let u = Handle::pack(path[i].0, path[i].1 == Direction::Left);
                let v = Handle::pack(path[i + 1].0, path[i + 1].1 == Direction::Left);
                if del_subg.edge_deleted(&u, &v) {
                    panic!(
                        "edge {}{} is flagged as deleted new graph",
                        v2str(&u),
                        v2str(&v)
                    );
                }
            }
        } else {
            let v = Handle::pack(path[0].0, path[0].1 == Direction::Left);
            if del_subg.node_deleted(&v) {
                panic!("node {} is flagged as deleted new graph", v2str(&v));
            }
        }

        // not all nodes of the transformation table are "old" nodes, but some have been created
        // by the affix-reduction
        let v = Handle::pack(*vid, false);
        if old_graph.has_node(v.id()) && old_graph.node_len(v) == *vlen {
            let old_seq = old_graph.sequence_vec(v);
            let new_seq = spell_walk(new_graph, path);
            if old_seq != new_seq {
                panic!(
                    "node {} in old graph spells sequence {}, but walk {} in new graph spell sequence {}",
                    vid,
                    String::from_utf8(old_seq).unwrap(),
                    path.iter().par_bridge()
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
    });
}

fn print_transformations<W: Write>(
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    orig_node_lens: &FxHashMap<usize, usize>,
    out: &mut io::BufWriter<W>,
) -> Result<(), io::Error> {
    writeln!(
        out,
        "{}",
        ["original_node", "transformed_walk", "bp_length"].join("\t")
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

fn spell_walk(graph: &HashGraph, walk: &[(usize, Direction, usize)]) -> Vec<u8> {
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
    let parents: Vec<String> = affix.parents.iter().map(v2str).collect();
    let children: Vec<String> = affix.shared_prefix_nodes.iter().map(v2str).collect();
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

fn parse_and_transform_paths<W: io::Write, T: OptFields>(
    gfa: &GFA<usize, T>,
    orig_node_lens: &FxHashMap<usize, usize>,
    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
    walks: &FxHashMap<Vec<u8>, Vec<u8>>,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    for path in gfa.paths.iter() {
        log::debug!("transforming path {}", str::from_utf8(&path.path_name)?);
        if walks.contains_key(&path.path_name[..]) {
            writeln!(
                out,
                "W\t{}\t{}",
                str::from_utf8(walks.get(&path.path_name[..]).unwrap())?,
                path.iter()
                    .map(|(sid, o)| {
                        transform_node(sid, o, *orig_node_lens.get(&sid).unwrap(), transform)
                            .into_iter()
                            .map(|(vid, d)| {
                                format!("{}{}", if d == Direction::Right { '>' } else { '<' }, vid)
                            })
                    })
                    .flatten()
                    .collect::<Vec<String>>()
                    .join("")
            )?;
        } else {
            writeln!(
                out,
                "P\t{}\t{}\t{}",
                str::from_utf8(&path.path_name)?,
                path.iter()
                    .map(|(sid, o)| {
                        transform_node(sid, o, *orig_node_lens.get(&sid).unwrap(), transform)
                            .into_iter()
                            .map(|(vid, d)| {
                                format!("{}{}", vid, if d == Direction::Right { '+' } else { '-' })
                            })
                    })
                    .flatten()
                    .collect::<Vec<String>>()
                    .join(""),
                path.overlaps
                    .iter()
                    .par_bridge()
                    .map(|x| match x {
                        None => "*".to_string(),
                        Some(c) => c.to_string(),
                    })
                    .collect::<Vec<String>>()
                    .join("")
            )?;
        }
    }

    Ok(())
}

fn parse_header<R: io::Read>(mut data: io::BufReader<R>) -> Result<Vec<u8>, io::Error> {
    let mut buf = vec![];
    while data.read_until(b'\n', &mut buf)? > 0 {
        if buf[0] == b'H' {
            // remove trailing new line character
            if buf.last() == Some(&b'\n') {
                buf.pop();
            }
            break;
        }
        buf.clear();
    }
    Ok(buf)
}

fn count_copies(
    visited_nodes: &mut FxHashMap<usize, usize>,
    visited_edges: &mut FxHashMap<Edge, usize>,
    path: &Vec<(usize, Direction)>,
) {
    for i in 1..path.len() {
        let (u, ou) = path[i - 1];
        let (v, ov) = path[i];
        visited_nodes.get_mut(&u).map(|x| *x += 1);

        let e = Edge::edge_handle(
            Handle::pack(u, ou == Direction::Left),
            Handle::pack(v, ov == Direction::Left),
        );
        visited_edges.get_mut(&e).map(|x| *x += 1);
    }
    if let Some((v, _)) = path.last() {
        visited_nodes.get_mut(&v).map(|x| *x += 1);
    }
}

//fn remove_unused_copies<R: io::Read, T: OptFields>(
//    copies: &Vec<usize>,
//    graph: &HashGraph,
//    mut data: io::BufReader<R>,
//    gfa: &GFA<usize, T>,
//    orig_node_lens: &FxHashMap<usize, usize>,
//    transform: &FxHashMap<(usize, usize), Vec<(usize, Direction, usize)>>,
//    del_subg: &mut DeletedSubGraph,
//) -> (usize, usize) {
//    // construct hashmap for counting the visits of edges introduced by the duplication process
//    let mut visited_edges = FxHashMap::default();
//    for i in copies.iter() {
//        let v = Handle::pack(*i, false);
//        for w in graph.neighbors(v, Direction::Left) {
//            visited_edges.insert(Edge::edge_handle(w, v), 0);
//        }
//        for w in graph.neighbors(v, Direction::Right) {
//            visited_edges.insert(Edge::edge_handle(v, w), 0);
//        }
//    }
//
//    // construct hashmap to count visits to nodes
//    let mut visited_nodes: FxHashMap<usize, usize> =
//        FxHashMap::from_iter(copies.iter().cloned().zip(repeat(0)));
//
//    for path in gfa.paths.iter() {
//        let tpath = transform_path(
//            &path
//                .iter()
//                .map(|(sid, o)| {
//                    (
//                        sid,
//                        match o {
//                            Orientation::Forward => Direction::Right,
//                            Orientation::Backward => Direction::Left,
//                        },
//                        *orig_node_lens.get(&sid).unwrap(),
//                    )
//                })
//                .collect::<Vec<(usize, Direction, usize)>>()[..],
//            transform,
//        );
//        count_copies(&mut visited_nodes, &mut visited_edges, &tpath);
//    }
//
//    // counters for removed nodes and edges
//    let mut cv = 0;
//    let mut ce = 0;
//
//    for (i, c) in visited_nodes.iter() {
//        if *c == 0 {
//            log::debug!("Removing unused duplicate node {}", i);
//            del_subg.add_node(Handle::pack(*i, false));
//            cv += 1;
//        }
//    }
//
//    for (Edge(u, v), c) in visited_edges.iter() {
//        if *c == 0 {
//            log::debug!("Removing unused duplicate edge {}{}", v2str(u), v2str(v));
//            // we don't need Edge::edge_handle here, because edges in visited_edges are already
//            // canonical
//            del_subg.add_edge(Edge(*u, *v));
//            ce += 1;
//        }
//    }
//
//    (cv, ce)
//}

fn parse_gfa_v12<R: io::Read>(
    data: io::BufReader<R>,
) -> (GFA<usize, ()>, FxHashMap<Vec<u8>, Vec<u8>>) {
    let parser = GFAParser::new();

    let mut walks = FxHashMap::default();
    // TODO
    //
    let lines: Vec<Vec<u8>> = ByteLineReader::new(data)
        .into_iter()
        .map(|x| transform_walks(x, &mut walks))
        .collect();
    let gfa: GFA<usize, ()> = parser.parse_lines(lines.iter().map(|x| &x[..])).unwrap();

    (gfa, walks)
}

fn main() -> Result<(), io::Error> {
    env_logger::init();

    // print output to stdout
    let mut out = io::BufWriter::new(std::io::stdout());

    // initialize command line parser & parse command line arguments
    let params = Command::parse();

    if params.threads > 0 {
        log::info!("running panacus on {} threads", &params.threads);
        rayon::ThreadPoolBuilder::new()
            .num_threads(params.threads)
            .build_global()
            .unwrap();
    } else {
        log::info!("running panacus using all available CPUs");
        rayon::ThreadPoolBuilder::new().build_global().unwrap();
    }

    // check if regex of no_collapse_path is valid
    if !params.no_collapse_path.trim().is_empty() && Regex::new(&params.no_collapse_path).is_err() {
        panic!(
            "Supplied string \"{}\" is not a valid regular expression",
            params.no_collapse_path
        );
    }

    log::info!("loading graph {}", &params.graph);
    let (mut gfa, walks) = parse_gfa_v12(io::BufReader::new(fs::File::open(&params.graph)?));

    //
    // REMOVING PATHS FROM GRAPH -- they SUBSTANTIALLY slow down graph editing
    //
    //
    let mut paths = Vec::new();
    std::mem::swap(&mut gfa.paths, &mut paths);

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
    if !params.no_collapse_path.trim().is_empty() {
        let re = Regex::new(&params.no_collapse_path).unwrap();
        for path in paths.iter() {
            let path_name = str::from_utf8(&path.path_name[..]).unwrap();
            if re.is_match(path_name) {
                dont_collapse_nodes.extend(
                    path.iter()
                        .map(|(xid, _)| (xid, *node_lens.get(&xid).unwrap())),
                );

                log::info!(
                    "flagging nodes of path {} as non-collapsing, total number is now at {}",
                    path_name,
                    dont_collapse_nodes.len()
                );
            }
        }
    }

    log::info!("identifying walk-preserving shared affixes");
    // yes, that's a "prefix", not an affix--because nodes are oriented accordingly
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

    let (affixes, mut del_subg, mut event_tracker) =
        find_and_collapse_walk_preserving_shared_affixes(&mut graph, &dont_collapse_nodes);

    //    log::info!("identifying walk-preserving blunt ends");
    //    find_and_collapse_blunt_ends(&mut graph, &mut del_subg, &mut event_tracker);

    for affix in affixes {
        print(&affix, &mut out)?;
    }

    if !dont_collapse_nodes.is_empty() {
        log::info!("de-collapse no-collapse handles and update transformation table");
        let copies = event_tracker.decollapse(&mut graph, &mut del_subg);
        //        let old_graph = HashGraph::from_gfa(&gfa);
        //
        //        let data = io::BufReader::new(fs::File::open(&params.graph)?);
        //        log::info!("cleaning up copies created during de-duplication...");
        //        let (cv, ce) = remove_unused_copies(
        //            &copies,
        //            &graph,
        //            data,
        //            &gfa,
        //            &node_lens,
        //            &event_tracker.get_expanded_transformation(),
        //            &mut del_subg,
        //        );
        //        log::info!("...removed {} unused duplicated nodes and {} edges", cv, ce);
    }

    log::info!("expand transformation table");
    let transform = event_tracker.get_expanded_transformation();

    if params.check_transformation {
        log::info!("checking correctness of applied transformations...");

        let old_graph = HashGraph::from_gfa(&gfa);
        check_transform(&old_graph, &graph, &transform, &del_subg);
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
        let data = io::BufReader::new(fs::File::open(&params.graph)?);
        let header = parse_header(data)?;
        writeln!(
            graph_out,
            "{}",
            if header.is_empty() {
                "H\tVN:Z:1.1"
            } else {
                str::from_utf8(&header[..]).unwrap()
            }
        )?;
        if let Err(e) = print_active_subgraph(&graph, &del_subg, &mut graph_out) {
            panic!(
                "unable to write refined graph to {}: {}",
                params.refined_graph_out, e
            );
        }

        // swap paths back in to produce final output
        std::mem::swap(&mut gfa.paths, &mut paths);
        log::info!("transforming paths+walks");
        if let Err(e) =
            parse_and_transform_paths(&gfa, &node_lens, &transform, &walks, &mut graph_out)
        {
            panic!(
                "unable to write refined GFA path+walk lines to {}: {}",
                params.refined_graph_out, e
            );
        };
    }
    out.flush()?;
    log::info!("done");
    Ok(())
}
