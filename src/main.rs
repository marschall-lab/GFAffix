/* standard use */
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use std::error::Error;
use std::io;
use std::io::prelude::*;

/* crate use */
use clap::Clap;
use gfa::{
    gfa::{Orientation, GFA},
    parser::GFAParser,
};
use handlegraph::{
    handle::{Direction, Edge, Handle},
    handlegraph::*,
    hashgraph::HashGraph,
    mutablehandlegraph::{AdditiveHandleGraph, MutableHandles},
};

#[derive(clap::Clap, Debug)]
#[clap(
    version = "0.1",
    author = "Daniel Doerr <daniel.doerr@hhu.de>",
    about = "Identify shared suffixes/prefixes in branchings"
)]
pub struct Command {
    #[clap(index = 1, about = "graph in GFA1 format", required = true)]
    pub graph: String,
}

// structure for storing reported subgraph
pub struct AffixSubgraph {
    pub sequence: String,
    pub parents: Vec<Handle>,
    pub shared_prefix_nodes: Vec<Handle>,
}

#[derive(Clone, Debug)]
pub struct DeletedSubGraph {
    pub edges: FxHashSet<(Handle, Handle)>,
    pub nodes: FxHashSet<Handle>,
}

impl DeletedSubGraph {
    fn add_edge(&mut self, u: Handle, v: Handle) -> bool {
        self.edges.insert(if u < v { (u, v) } else { (v, u) })
    }

    fn add_node(&mut self, v: Handle, graph: &HashGraph) -> bool {
        let mut res = false;
        res |= self.nodes.insert(v);
        res |= self.nodes.insert(v.flip());

        for u in graph
            .neighbors(v, Direction::Left)
            .chain(graph.neighbors(v, Direction::Right))
        {
            res |= self.add_edge(u, v);
        }
        res
    }

    fn new() -> Self {
        DeletedSubGraph {
            edges: FxHashSet::default(),
            nodes: FxHashSet::default(),
        }
    }
}

fn enumerate_variant_preserving_shared_affixes(
    graph: &HashGraph,
    v: Handle,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    let mut res: Vec<AffixSubgraph> = Vec::new();

    let mut branch: FxHashMap<(u8, Vec<Handle>), Vec<Handle>> = FxHashMap::default();
    // traverse multifurcation in the forward direction of the handle
    for u in graph.neighbors(v, Direction::Right) {
        let seq = graph.sequence_vec(u);

        // get parents of u
        let mut parents: Vec<Handle> = graph.neighbors(u, Direction::Left).collect();
        parents.sort();
        // insert child in variant-preserving data structure
        branch
            .entry((seq[0], parents))
            .or_insert(Vec::new())
            .push(u);
    }

    for ((_, parents), children) in branch.iter() {
        if children.len() > 1 {
            res.push(AffixSubgraph {
                sequence: get_shared_prefix(children, graph)?,
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
) -> Handle {
    let prefix_len = shared_prefix.sequence.len();

    // update graph in two passes:
    //  1. split nodes into shared prefix and distinct suffix and appoint dedicated shared
    //  prefix node
    let mut shared_prefix_node_maybe: Option<Handle> = None;
    let mut splitted_node_pairs: Vec<(Handle, Option<Handle>)> = Vec::new();
    for v in shared_prefix.shared_prefix_nodes.iter() {
        if graph.sequence_vec(*v).len() < prefix_len {
            // x corresponds to the shared prefix,
            let (x, u) = graph.split_handle(*v, prefix_len);
            splitted_node_pairs.push((x, Some(u)));
            // update dedicated shared prefix node if none has been assigned yet
            if shared_prefix_node_maybe == None {
                shared_prefix_node_maybe = Some(x);
            }
            log::debug!(
                "splitting node {}{} into prefix {}{} and suffix {}{}",
                if v.is_reverse() { '<' } else { '>' },
                usize::from(v.id()),
                if x.is_reverse() { '<' } else { '>' },
                usize::from(x.id()),
                if u.is_reverse() { '<' } else { '>' },
                usize::from(u.id())
            );
        } else {
            // always use a node as dedicated shared prefix node if that node coincides with the
            // prefix
            shared_prefix_node_maybe = Some(*v);
            splitted_node_pairs.push((*v, None));
            log::debug!(
                "node {}{} matches prefix {}",
                if v.is_reverse() { '<' } else { '>' },
                usize::from(v.id()),
                &shared_prefix.sequence
            );
        }
    }

    //  2. update deleted edge set, reassign outgoing edges of "empty" nodes to dedicated shared
    //     prefix node
    let mut shared_prefix_node = Handle::new(usize::MAX-2, Orientation::Forward);
    if let Some(v) = shared_prefix_node_maybe {
        // there will be always a shared prefix node, so this condition is always true
        shared_prefix_node = v;
        log::debug!(
            "node {}{} is dedicated shared prefix node",
            if v.is_reverse() { '<' } else { '>' },
            usize::from(v.id())
        );
    }
    for (u, maybe_v) in splitted_node_pairs {
        if u != shared_prefix_node {
            // mark redundant node as deleted
            del_subg.add_node(u, &graph);

            // rewrire outgoing edges
            match maybe_v {
                Some(v) => {
                    // make all suffixes spring from shared suffix node
                    graph.create_edge(Edge(shared_prefix_node, v));
                    log::debug!(
                        "create edge {}{}-{}{}",
                        if shared_prefix_node.is_reverse() {
                            '<'
                        } else {
                            '>'
                        },
                        usize::from(shared_prefix_node.id()),
                        if v.is_reverse() { '<' } else { '>' },
                        usize::from(v.id())
                    );
                }
                None => {
                    // if node coincides with shared prefix (but is not the dedicated shared prefix
                    // node), then all outgoing edges of this node must be transferred to dedicated
                    // node
                    let outgoing_edges: Vec<Handle> =
                        graph.neighbors(u, Direction::Right).collect();
                    for w in outgoing_edges {
                        graph.create_edge(Edge(shared_prefix_node, w));
                        log::debug!(
                            "create edge {}{}-{}{}",
                            if shared_prefix_node.is_reverse() {
                                '<'
                            } else {
                                '>'
                            },
                            usize::from(shared_prefix_node.id()),
                            if w.is_reverse() { '<' } else { '>' },
                            usize::from(w.id())
                        );
                    }
                }
            }
        }
    }

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
        if sequences
            .iter()
            .any(|other| other.len() <= i || other[i] != c)
        {
            break;
        }
        seq.push(c);
        i += 1;
    }

    String::from_utf8(seq)
}

fn find_and_report_variant_preserving_shared_affixes<W: Write>(
    graph: &mut HashGraph,
    out: &mut io::BufWriter<W>,
) -> Result<DeletedSubGraph, Box<dyn Error>> {
    let mut del_subg = DeletedSubGraph::new();

    let mut queue: Vec<Handle> = Vec::new();
    queue.extend(graph.handles().chain(graph.handles().map(|v| v.flip())));
    while let Some(v) = queue.pop() {
        if !del_subg.nodes.contains(&v) {
            log::debug!(
                "processing oriented node {}{}",
                if v.is_reverse() { '<' } else { '>' },
                usize::from(v.id())
            );

            // process node in forward direction
            let affixes = enumerate_variant_preserving_shared_affixes(graph, v)?;
            for affix in affixes.iter() {
                print(affix, out)?;
                let shared_prefix_node = collapse(graph, affix, &mut del_subg);
                queue.push(shared_prefix_node);
                queue.push(shared_prefix_node.flip());
            }
        }
    }

    Ok(del_subg)
}

fn print<W: io::Write>(affix: &AffixSubgraph, out: &mut io::BufWriter<W>) -> Result<(), io::Error> {
    let parents: Vec<String> = affix
        .parents
        .iter()
        .map(|&v| {
            format!(
                "{}{}",
                if v.is_reverse() { '<' } else { '>' },
                usize::from(v.id()),
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
                usize::from(v.id()),
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

    log::info!("identifying variant-preserving shared prefixes");
    writeln!(
        out,
        "{}",
        [
            "oriented_start_node",
            "oriented_end_nodes",
            "prefix_length",
            "prefix",
        ]
        .join("\t")
    )?;
    if let Err(e) = find_and_report_variant_preserving_shared_affixes(&mut graph, &mut out) {
        panic!("gfaffix failed: {}", e);
    }
    out.flush()?;
    log::info!("done");
    Ok(())
}
