/* standard use */
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use std::error::Error;
use std::fs;
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
    about = "Identify shared suffixes/prefixes in multifurcaitons of the given graph.\n\n
    Want log output? Call program with 'RUST_LOG=info gfaffix ...'\n 
    Log output not informative enough? Call program with 'RUST_LOG=debug gfaffix..."
)]
pub struct Command {
    #[clap(index = 1, about = "graph in GFA1 format", required = true)]
    pub graph: String,

    #[clap(
        short = 'o',
        long = "output_refined",
        about = "output refined graph in GFA1 format",
        default_value = " "
    )]
    pub refined_graph_out: String,
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
        let is_insert = self.edges.insert(if u < v { (u, v) } else { (v, u) });
        if is_insert {
            let (x, y) = if u < v { (u, v) } else { (v, u) };
            log::debug!(
                "flag edge {}{}-{}{} as deleted",
                if x.is_reverse() { '<' } else { '>' },
                usize::from(x.id()),
                if y.is_reverse() { '<' } else { '>' },
                usize::from(y.id())
            );
        }
        is_insert
    }

    fn add_node(&mut self, v: Handle, graph: &HashGraph) -> bool {
        let mut res = false;
        res |= self.nodes.insert(v);
        res |= self.nodes.insert(v.flip());

        for u in graph.neighbors(v, Direction::Left) {
            res |= self.add_edge(u.flip(), v.flip());
        }
        for u in graph.neighbors(v, Direction::Right) {
            res |= self.add_edge(u.flip(), v);
        }
        res
    }

    fn is_deleted(&self, u: &Handle, v: &Handle) -> bool {
        let e = if u < v { (*u, *v) } else { (*v, *u) };
        self.edges.contains(&e)
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
    del_subg: &DeletedSubGraph,
    v: Handle,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    let mut res: Vec<AffixSubgraph> = Vec::new();

    let mut branch: FxHashMap<(u8, Vec<Handle>), Vec<Handle>> = FxHashMap::default();
    // traverse multifurcation in the forward direction of the handle
    for u in graph.neighbors(v, Direction::Right) {
        if !del_subg.is_deleted(&v, &u) {
            let seq = graph.sequence_vec(u);

            // get parents of u
            let mut parents: Vec<Handle> = graph
                .neighbors(u, Direction::Left)
                .filter(|w| !del_subg.is_deleted(&u.flip(), w))
                .collect();
            parents.sort();
            // insert child in variant-preserving data structure
            branch
                .entry((seq[0], parents))
                .or_insert(Vec::new())
                .push(u);
        }
    }

    for ((_, parents), children) in branch.iter() {
        if children.len() > 1 {
            log::debug!(
                "identified shared prefix between nodes {} originating from parents {}",
                children
                    .iter()
                    .map(|v| format!(
                        "{}{}",
                        if v.is_reverse() { '<' } else { '>' },
                        usize::from(v.id())
                    ))
                    .collect::<Vec<String>>()
                    .join(","),
                parents
                    .iter()
                    .map(|v| format!(
                        "{}{}",
                        if v.is_reverse() { '<' } else { '>' },
                        usize::from(v.id())
                    ))
                    .collect::<Vec<String>>()
                    .join(",")
            );
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
    let mut shared_prefix_node = Handle::new(0, Orientation::Forward);
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
            // rewrire outgoing edges
            match maybe_v {
                Some(v) => {
                    // make all suffixes spring from shared suffix node
                    if !graph.has_edge(shared_prefix_node, v) {
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
                }
                None => {
                    // if node coincides with shared prefix (but is not the dedicated shared prefix
                    // node), then all outgoing edges of this node must be transferred to dedicated
                    // node
                    let outgoing_edges: Vec<Handle> = graph
                        .neighbors(u, Direction::Right)
                        .filter(|v| !del_subg.is_deleted(&u, v))
                        .collect();
                    for w in outgoing_edges {
                        if !graph.has_edge(shared_prefix_node, w) {
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
            // mark redundant node as deleted
            log::debug!(
                "flag {}{} as deleted",
                if u.is_reverse() { '<' } else { '>' },
                usize::from(u.id())
            );
            del_subg.add_node(u, &graph);
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
            let affixes = enumerate_variant_preserving_shared_affixes(graph, &del_subg, v)?;
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

fn print_active_subgraph<W: io::Write>(
    graph: &HashGraph,
    del_subg: &DeletedSubGraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), Box<dyn Error>> {
    for v in graph.handles() {
        if !del_subg.nodes.contains(&v) {
            writeln!(
                out,
                "S\t{}\t{}",
                usize::from(v.id()),
                String::from_utf8(graph.sequence_vec(v))?
            )?;
        }
    }
    for Edge(u, v) in graph.edges() {
        if !del_subg.is_deleted(&u, &v) {
            writeln!(
                out,
                "L\t{}\t{}\t{}\t{}\t0M",
                usize::from(u.id()),
                if u.is_reverse() { '-' } else { '+' },
                usize::from(v.id()),
                if v.is_reverse() { '-' } else { '+' }
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

    log::info!("identifying variant-preserving shared prefixes");
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
    let res = find_and_report_variant_preserving_shared_affixes(&mut graph, &mut out);

    match res {
        Err(e) => panic!("gfaffix failed: {}", e),
        Ok(del_subg) => {
            if !params.refined_graph_out.trim().is_empty() {
                let mut graph_out =
                    io::BufWriter::new(fs::File::create(params.refined_graph_out.clone())?);
                if let Err(e) = print_active_subgraph(&graph, &del_subg, &mut graph_out) {
                    panic!(
                        "unable to write refined graph to {}: {}",
                        params.refined_graph_out.clone(),
                        e
                    );
                }
            }
        }
    }
    out.flush()?;
    log::info!("done");
    Ok(())
}
