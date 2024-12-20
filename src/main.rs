/* standard use */
use std::collections::{HashSet, VecDeque};
use std::error::Error;
use std::fs;
use std::io::prelude::*;
use std::io;
use std::iter::FromIterator;
use std::str;

/* crate use */
use clap::{crate_version, Parser};
use flate2::{read::MultiGzDecoder, write::GzEncoder, Compression};
use env_logger::Env;
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
};
use indexmap::{IndexMap, IndexSet};
use rayon::prelude::*;
use regex::Regex;
use rustc_hash::{FxBuildHasher, FxHashMap, FxHashSet};

/* mod declaration */
mod collapse_event_tracker;
use collapse_event_tracker::*;
mod affix_sub_graph;
use affix_sub_graph::*;
mod deleted_sub_graph;
use deleted_sub_graph::*;
mod walk_transform;
use walk_transform::*;

const EXPLORE_NEIGHBORHOOD: usize = 2;
type FxIndexMap<K, V> = IndexMap<K, V, FxBuildHasher>;
type FxIndexSet<V> = IndexSet<V, FxBuildHasher>;

type OrientedNode = (usize, Direction, usize);
type Node = (usize, usize);

#[derive(Parser, Debug)]
#[clap(
    version = crate_version!(),
    author = "Daniel Doerr <daniel.doerr@hhu.de>",
    about = "Discover and collapse walk-preserving shared affixes of a given variation graph."
)]
pub struct Command {
    #[clap(index = 1, help = "graph in GFA1 format, supports compressed (.gz) input", required = true)]
    pub graph: String,

    #[clap(
        short = 'o',
        long = "output_refined",
        help = "Write refined graph output (GFA1 format) to supplied file instead of stdout; if file name ends with .gz, output will be compressed",
        default_value = "" 
    )]
    pub refined_graph_out: String,

    #[clap(
        short = 't',
        long = "output_transformation",
        help = "Report original nodes and their corresponding walks in refined graph to supplied file",
        default_value = "" 
    )]
    pub transformation_out: String,

    #[clap(
        short = 'c',
        long = "check_transformation",
        help = "Verifies that the transformed parts of the graphs spell out the identical sequence as in the original graph",
    )]
    pub check_transformation: bool,

    #[clap(
        short = 'a',
        long = "output_affixes",
        help = "Report identified affixes",
        default_value = "" 
    )]
    pub affixes_out: String,

    #[clap(
        short = 'x',
        long = "dont_collapse",
        help = "Do not collapse nodes on a given paths (\"P\" lines) that match given regular expression",
        default_value = "" 
    )]
    pub no_collapse_path: String,

    #[clap(
        short = 'p',
        long,
        help = "Run in parallel on N threads",
        default_value = "1"
    )]
    threads: usize,

    #[clap(short = 'v', long, help = "Sets log level to debug")]
    verbose: bool,
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
            let children = branch.entry((c, parents)).or_default();

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
                        parents,
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
    let mut original_edges: Vec<(OrientedNode, Vec<OrientedNode>)> = Vec::new();
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
        let is_dont_collapse = event_tracker
            .dont_collapse_nodes
            .contains(&(node_id, v_len));
        if is_dont_collapse {
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
            if is_dont_collapse {
                let last = original_edges.last().unwrap();
                log::debug!(
                    "registering >{}:{} as dont-collapse-node",
                    last.0 .0,
                    last.0 .2
                );
                event_tracker
                    .dont_collapse_nodes
                    .insert((last.0 .0, last.0 .2));
                log::debug!(
                    "registering >{}:{} as dont-collapse-node",
                    last.1[0].0,
                    last.1[0].2
                );
                event_tracker
                    .dont_collapse_nodes
                    .insert((last.1[0].0, last.1[0].2));
            }
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

                    if is_dont_collapse {
                        let wid = w.unpack_number() as usize;
                        log::debug!("registering >{}:{} as dont-collapse-node", wid, prefix_len);
                        event_tracker.dont_collapse_nodes.insert((wid, prefix_len));
                    }
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
                Some(enumerate_walk_preserving_shared_affixes(graph, del_subg, *v).unwrap())
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

    while let Some((d, v)) = queue.pop() {
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
    dont_collapse_nodes: &FxIndexSet<Node>,
    v: Handle,
) -> Option<Handle> {
    if del_subg.node_deleted(&v) || graph.degree(v, Direction::Left) > 0 {
        None
    } else {
        let l = graph.node_len(v);
        graph
            .neighbors(v, Direction::Right)
            .filter_map(|u| {
                if del_subg.node_deleted(&u) || del_subg.edge_deleted(&u, &v) {
                    None
                } else {
                    graph.neighbors(u, Direction::Left).find(|&w| {
                        !del_subg.node_deleted(&w)
                            && !del_subg.edge_deleted(&w, &u)
                            && w != v
                            && !(dont_collapse_nodes
                                .contains(&(w.unpack_number() as usize, graph.node_len(w)))
                                && dont_collapse_nodes
                                    .contains(&(v.unpack_number() as usize, graph.node_len(v))))
                            && get_shared_prefix(&[w.flip(), v.flip()], graph)
                                .unwrap()
                                .len()
                                == l
                            && HashSet::<Handle>::from_iter(graph.neighbors(v, Direction::Right))
                                .is_subset(&HashSet::from_iter(
                                    graph.neighbors(w, Direction::Right),
                                ))
                    })
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
            .filter_map(|&v| {
                find_collapsible_blunt_end_pair(
                    graph,
                    del_subg,
                    event_tracker.dont_collapse_nodes,
                    v,
                )
                .map(|u| (v, u))
            })
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
                    log::debug!(
                        "found collapsible blunt end node {} of length {} matching prefix {}",
                        v2str(&v),
                        prefix.len() + 1,
                        v2str(&u)
                    );
                    // parent set is not potentially not identical, but we need to make it so that
                    // it works
                    // TODO
//                    for graph.neighbors(v, Direction::Right) {
//                            .is_subset(&HashSet::from_iter(
//                                graph.neighbors(w, Direction::Right),
//                            ))
//                    }
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
    dont_collapse_nodes: &'a mut FxIndexSet<(usize, usize)>,
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
            let mut cur_affixes = find_walk_preserving_shared_affixes(graph, &del_subg, queue);
            cur_affixes.sort_by_cached_key(|x| {
                (-(x.sequence.len() as i64), *x.parents.iter().min().unwrap())
            });
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
                    // 1 iteration is enough?
                    //                    has_changed |= true;
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

fn transform_node(
    vid: usize,
    orient: Orientation,
    v_len: usize,
    transform: &FxHashMap<Node, Vec<OrientedNode>>,
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
    transform: &FxHashMap<Node, Vec<OrientedNode>>,
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
                let w = Handle::pack(path[i + 1].0, path[i + 1].1 == Direction::Left);
                if !new_graph.has_edge(u, w) {
                    panic!(
                        "error in rule >{}:{}, graph does not contain edge {}{}",
                        vid,
                        vlen,
                        v2str(&u),
                        v2str(&w)
                    );
                }
                if del_subg.edge_deleted(&u, &w) {
                    panic!(
                        "error in rule >{}:{}, edge {}{} is flagged as deleted new graph",
                        vid,
                        vlen,
                        v2str(&u),
                        v2str(&w)
                    );
                }
                if del_subg.node_deleted(&u) {
                    panic!(
                        "error in rule >{}:{}, node {} is flagged as deleted new graph",
                        vid,
                        vlen,
                        v2str(&u),
                    );
                }
                if del_subg.node_deleted(&w) {
                    panic!(
                        "error in rule >{}:{}, node {} is flagged as deleted new graph",
                        vid,
                        vlen,
                        v2str(&w),
                    );
                }
            }
        } else {
            let w = Handle::pack(path[0].0, path[0].1 == Direction::Left);
            if del_subg.node_deleted(&w) {
                panic!("error in rule >{}:{}, node {} is flagged as deleted new graph", vid, vlen, v2str(&w));
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
            // todo: also check for edges on the other side
            for u in old_graph.neighbors(v, Direction::Left) {
                let ulen = old_graph.node_len(u);
                let x = Handle::pack(path[0].0, path[0].1 == Direction::Left);
                let w = match transform.get(&(u.unpack_number() as usize, ulen)) {
                    Some(w) => if u.is_reverse() {
                        let (wid, worient, _) = *w.first().unwrap();
                        Handle::pack(wid as u64, worient == Direction::Right)
                    } else {
                        let (wid, worient, _) = *w.last().unwrap();
                        Handle::pack(wid as u64, worient == Direction::Left)
                    },
                    None => u
                };
                if !new_graph.has_edge(w, x) || del_subg.edge_deleted(&w, &x) {
                    panic!("edge {}{} in old graph either does not have counterpart {}{} in new graph, or edge is flagged as deleted", v2str(&u), v2str(&v), v2str(&w), v2str(&x));
                }
            }
        }
    });
}

fn print_transformations<W: Write>(
    transform: &FxHashMap<Node, Vec<OrientedNode>>,
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

fn spell_walk(graph: &HashGraph, walk: &[OrientedNode]) -> Vec<u8> {
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
    transform: &FxHashMap<Node, Vec<OrientedNode>>,
    walks: &FxHashMap<Vec<u8>, Vec<u8>>,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    let mut out_b: Vec<u8> = Vec::new();
    for path in gfa.paths.iter() {
        let l = path.segment_names.len();
        if out_b.capacity() < l {
            out_b.reserve(l - out_b.capacity());
        }
        if let Some(walk_name_u8) = walks.get(&path.path_name[..]) {
            log::debug!(
                "transforming walk {}",
                str::from_utf8(&path.path_name[..path.path_name.len() - 8])?
            );
            write!(out, "W\t{}\t", str::from_utf8(walk_name_u8)?)?;
            for (sid, o) in path.iter() {
                for (vid, d) in
                    transform_node(sid, o, *orig_node_lens.get(&sid).unwrap(), transform)
                {
                    out_b.push(if d == Direction::Right { b'>' } else { b'<' });
                    out_b.extend_from_slice(vid.to_string().as_bytes());
                }
            }
            out.write_all(&out_b[..])?;
            writeln!(out)?;
        } else {
            let path_name = str::from_utf8(&path.path_name)?;
            log::debug!("transforming path {}", path_name);
            for (sid, o) in path.iter() {
                for (vid, d) in
                    transform_node(sid, o, *orig_node_lens.get(&sid).unwrap(), transform)
                {
                    out_b.extend_from_slice(vid.to_string().as_bytes());
                    out_b.push(if d == Direction::Right { b'+' } else { b'-' });
                    out_b.push(b',');
                }
            }
            // remove last ","
            out_b.pop();
            write!(out, "P\t{}\t", path_name)?;
            out.write_all(&out_b[..])?;
            writeln!(out, "\t*")?;
        }
        out_b.clear();
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

fn parse_gfa_v12<R: io::Read>(
    data: io::BufReader<R>,
) -> (GFA<usize, ()>, FxHashMap<Vec<u8>, Vec<u8>>) {
    let parser = GFAParser::new();

    let mut walks = FxHashMap::default();
    let lines: Vec<Vec<u8>> = ByteLineReader::new(data)
        .map(|x| transform_walks(x, &mut walks))
        .collect();
    let gfa: GFA<usize, ()> = parser.parse_lines(lines.iter().map(|x| &x[..])).unwrap();

    (gfa, walks)
}

fn main() -> Result<(), io::Error> {

    // initialize command line parser & parse command line arguments
    let params = Command::parse();

    // set up logging
    env_logger::Builder::from_env(Env::default().default_filter_or(if params.verbose {
        "debug"
    } else {
        "info"
    }))
    .init();

    // set up parallelization
    if params.threads > 0 {
        log::info!("running gfaffix on {} threads", &params.threads);
        rayon::ThreadPoolBuilder::new()
            .num_threads(params.threads)
            .build_global()
            .unwrap();
    } else {
        log::info!("running gfaffix using all available CPUs");
        rayon::ThreadPoolBuilder::new().build_global().unwrap();
    }

    // check if regex of no_collapse_path is valid
    if !params.no_collapse_path.is_empty() && Regex::new(&params.no_collapse_path).is_err() {
        panic!(
            "supplied string \"{}\" is not a valid regular expression",
            params.no_collapse_path
        );
    }

    log::info!("loading graph from {}", &params.graph);

    let f = std::fs::File::open(params.graph.clone()).expect("Error opening file");
    let reader: Box<dyn Read> = if params.graph.ends_with(".gz") {
        log::info!("assuming that {} is gzip compressed..", &params.graph);
        Box::new(MultiGzDecoder::new(f))
    } else {
        Box::new(f)
    };
    
    let (mut gfa, walks) = parse_gfa_v12(io::BufReader::new(reader));

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

    let mut dont_collapse_nodes: FxIndexSet<Node> = FxIndexSet::default();
    if !params.no_collapse_path.is_empty() {
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
    let (affixes, mut del_subg, mut event_tracker) =
        find_and_collapse_walk_preserving_shared_affixes(&mut graph, &mut dont_collapse_nodes);

    if !params.affixes_out.is_empty() {
        log::info!("writing affixes to {}", params.affixes_out);
        let mut aff_out = io::BufWriter::new(fs::File::create(params.affixes_out.clone())?);
        // yes, that's a "prefix", not an affix--because nodes are oriented accordingly
        writeln!(
            aff_out,
            "{}",
            [
                "oriented_parent_nodes",
                "oriented_child_nodes",
                "prefix_length",
                "prefix",
            ]
            .join("\t")
        )?;
        for affix in affixes {
            print(&affix, &mut aff_out)?;
        }
    }

    if !event_tracker.dont_collapse_nodes.is_empty() {
        log::info!("de-collapse no-collapse handles and update transformation table");
        event_tracker.decollapse(&mut graph, &mut del_subg);
    }

    // a blunt-end collapse is a non-symmetric operation, which cannot be reversed easily,
    // therefore we do this after decollapse (and make sure that we don't collapse reference nodes)
    log::info!("identifying walk-preserving blunt ends");
    find_and_collapse_blunt_ends(&mut graph, &mut del_subg, &mut event_tracker);

    log::info!("expand transformation table");
    let transform = event_tracker.get_expanded_transformation();

    if params.check_transformation {
        log::info!("checking correctness of applied transformations...");

        let old_graph = HashGraph::from_gfa(&gfa);
        check_transform(&old_graph, &graph, &transform, &del_subg);
        log::info!("all correct!");
    }

    if !params.transformation_out.is_empty() {
        log::info!("writing transformations to {}", params.transformation_out);
        let mut trans_out =
            io::BufWriter::new(fs::File::create(params.transformation_out.clone())?);
        if let Err(e) = print_transformations(&transform, &node_lens, &mut trans_out) {
            panic!("unable to write graph transformations to stdout: {}", e);
        }
    }


    // set up graph output stream
    let mut graph_out : io::BufWriter<Box<dyn Write>> = if params.refined_graph_out.is_empty() {
        if params.graph.ends_with(".gz") {
            log::info!("writing compressed refined graph to standard out");
            io::BufWriter::new(Box::new(GzEncoder::new(std::io::stdout(), Compression::new(5))))
        } else {
            log::info!("writing refined graph to standard out");
            io::BufWriter::new(Box::new(std::io::stdout()))
        }
    } else {
        if params.refined_graph_out.ends_with(".gz") {
            log::info!("writing compressed refined graph to {}", params.refined_graph_out);
            io::BufWriter::new(Box::new(GzEncoder::new(fs::File::create(params.refined_graph_out.clone())?, Compression::new(5))))
        } else {
            log::info!("writing refined graph to {}", params.refined_graph_out);
            io::BufWriter::new(Box::new(fs::File::create(params.refined_graph_out.clone())?))
        }
    };

    let f = std::fs::File::open(params.graph.clone()).expect("Error opening file");
    let reader: Box<dyn Read> = if params.graph.ends_with(".gz") {
        Box::new(MultiGzDecoder::new(f))
    } else {
        Box::new(f)
    };
    let header = parse_header(io::BufReader::new(reader))?;
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
    graph_out.flush()?;
    log::info!("done");
    Ok(())
}
