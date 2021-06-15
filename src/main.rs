/* standard use */
use rustc_hash::FxHashMap;
use rustc_hash::FxHashSet;
use std::error::Error;
use std::io;
use std::io::prelude::*;

/* crate use */
use clap::Clap;
use gfa::{gfa::GFA, parser::GFAParser};
use handlegraph::{
    handle::{Direction, Handle},
    handlegraph::*,
    hashgraph::HashGraph,
};

// fail-safe for complex circular structures
const MAX_EXTENSION: usize = 10_000;

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
    pub start: (usize, Direction, usize),
    pub ends: Vec<(usize, Direction, usize)>,
}

// structure storing a shared character
#[derive(Debug, Clone, Hash, Eq)]
pub struct SharedChar {
    pub parent: Option<usize>,
    pub positions: Vec<(Handle, usize)>,
    pub is_coalescing: bool,
}

impl SharedChar {
    fn safe_push(
        &mut self,
        graph: &HashGraph,
        v: Handle,
        position: usize,
    ) -> Result<(), Box<dyn Error>> {
        // check whether character matches the existing ones
        if !self.positions.is_empty() {
            if self.positions.contains(&(v, position)) {
                self.is_coalescing = true;
                return Ok(());
            }
            let (u, p) = self.positions.iter().next().unwrap();
            if graph.sequence_vec(*u)[*p] != graph.sequence_vec(v)[position] {
                panic!(
                    "character {} does not match {} of shared character",
                    graph.sequence_vec(v)[position] as char,
                    graph.sequence_vec(*u)[*p] as char
                )
            }
        }
        log::debug!("safely appending {:?}:{} to shared character", v, position);
        self.positions.push((v, position));
        Ok(())
    }

    fn new(parent: Option<usize>) -> SharedChar {
        SharedChar {
            parent: parent,
            positions: Vec::new(),
            is_coalescing: false,
        }
    }
}

impl PartialEq for SharedChar {
    fn eq(&self, other: &Self) -> bool {
        self.positions == other.positions
    }
}

fn build_shared_affix_dag(
    graph: &HashGraph,
    start: Handle,
    direction: Direction,
    visited: &mut FxHashSet<Handle>,
) -> Result<Vec<SharedChar>, Box<dyn Error>> {
    let mut res: Vec<SharedChar> = Vec::new();

    let mut visiting: FxHashSet<Handle> = FxHashSet::default();
    // create "root", corresponding to the character just before the multifurcation
    let mut root = SharedChar::new(None);
    root.safe_push(&graph, start, graph.sequence_vec(start).len() - 1)?;
    res.push(root);
    let mut i = 0;
    while i < res.len() && i < MAX_EXTENSION {
        let el = &res[i];
        let mut branch: FxHashMap<u8, SharedChar> = FxHashMap::default();
        let mut all_visited = true;
        for (v, p) in el.positions.iter() {
            // extend shared sequence
            if p + 1 < graph.sequence_vec(*v).len() {
                // traverse within node
                let seq = graph.sequence_vec(*v);
                let c = branch.entry(seq[p + 1]).or_insert(SharedChar::new(Some(i)));
                c.safe_push(&graph, *v, p + 1)?;
                all_visited = false;
            } else {
                // traverse multifurcation
                for u in graph.neighbors(*v, direction) {
                    all_visited &= !visiting.insert(u);
                    let seq = graph.sequence_vec(u);
                    let c = branch.entry(seq[0]).or_insert(SharedChar::new(Some(i)));
                    c.safe_push(&graph, u, 0)?;
                }
            }
        }

        if all_visited {
            log::debug!(
                "stopping cyclic traversal that started in {}{}:{}",
                if start.is_reverse() { '<' } else { '>' },
                usize::from(start.id()),
                graph.sequence_vec(start).len() - 1
            );
        } else {
            for (_, c) in branch.drain() {
                // allow for one more character to be processed if c is a coalescing node
                if c.positions.len() > 1 || c.is_coalescing {
                    res.push(c);
                } else if c.positions.len() == 1 {
                    // we haven't actually "visited" the node, so let's remove it from the visited
                    // list
                    visiting.remove(&c.positions[0].0);
                }
            }
        }
        i += 1;
    }
    if i >= MAX_EXTENSION {
        log::error!(
            "stopped after {} extensions from {}{}:{} to prevent cyclic traversal",
            MAX_EXTENSION,
            if start.is_reverse() { '<' } else { '>' },
            usize::from(start.id()),
            graph.sequence_vec(start).len() - 1
        )
    }
    // update visited handles
    visited.extend(visiting);
    Ok(res)
}

fn enumerate_shared_affix_subg(
    shared_affix_dag: &Vec<SharedChar>,
    graph: &HashGraph,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    // bottom-up processing of shared sequence dag
    let mut res: Vec<AffixSubgraph> = Vec::new();

    // don't continue if graph contains only root node
    if shared_affix_dag.len() <= 1 {
        return Ok(res);
    }
    // identify leaves of the DAG
    let child_count = get_child_count(&shared_affix_dag);

    log::debug!("child count: {:?}", child_count);

    // identify branchings of shared sequences
    // do not report coalescing paths (unless they cannot be further extended)
    let mut is_branching = vec![false; shared_affix_dag.len()];
    // ignore root
    for i in 1..is_branching.len() {
        if let Some(j) = shared_affix_dag[i].parent {
            is_branching[j] = shared_affix_dag[i].positions.len()
                < shared_affix_dag[j].positions.len()
                && !shared_affix_dag[i].is_coalescing
        }
    }

    // root is by definition the first character in shared_affix_dag
    let root = shared_affix_dag[0].positions[0];
    let start = (
        usize::from(root.0.id()),
        if root.0.is_reverse() {
            Direction::Left
        } else {
            Direction::Right
        },
        root.1,
    );

    for (i, c) in child_count.iter().enumerate() {
        if *c == 0 || is_branching[i] {
            let mut ends: Vec<(usize, Direction, usize)> = Vec::new();
            for (v, p) in &shared_affix_dag[i].positions {
                ends.push((
                    usize::from(v.id()),
                    if v.is_reverse() {
                        Direction::Left
                    } else {
                        Direction::Right
                    },
                    *p,
                ));
            }
            let sequence = get_sequence(shared_affix_dag, graph, i)?;
            res.push(AffixSubgraph {
                sequence,
                start,
                ends,
            });
        }
    }

    Ok(res)
}

fn get_sequence(
    shared_affix_dag: &Vec<SharedChar>,
    graph: &HashGraph,
    end: usize,
) -> Result<String, std::string::FromUtf8Error> {
    let mut seq: Vec<u8> = Vec::new();
    let mut p = &shared_affix_dag[end];
    seq.push(graph.sequence_vec(p.positions[0].0)[p.positions[0].1]);
    while let Some(i) = p.parent {
        p = &shared_affix_dag[i];
        seq.push(graph.sequence_vec(p.positions[0].0)[p.positions[0].1]);
    }

    seq.reverse();
    String::from_utf8(seq)
}

fn get_child_count(shared_affix_dag: &Vec<SharedChar>) -> Vec<usize> {
    let mut res: Vec<usize> = vec![0; shared_affix_dag.len()];
    // root at position 0 has no parent, so let's skip
    for i in 1..shared_affix_dag.len() {
        if let Some(p) = shared_affix_dag[i].parent {
            res[p] += 1;
        }
    }
    res
}

fn find_shared_affixes(
    graph: &HashGraph,
    direction: Direction,
) -> Result<Vec<AffixSubgraph>, Box<dyn Error>> {
    let mut res = Vec::new();

    let mut visited: FxHashSet<Handle> = FxHashSet::default();

    let oriented_nodes = graph.handles();
    for mut start in oriented_nodes {
        if usize::from(start.id()) < 1228465 || usize::from(start.id()) > 1228483 {
            continue
        }

        for _ in 0..2 {
            log::debug!(
                "processing oriented node {}{}",
                if start.is_reverse() { '<' } else { '>' },
                usize::from(start.id())
            );

            // process node in forward direction
            // make sure each multifurcation is tested only once
            if !visited.contains(&start) {
                let shared_affix_dag = build_shared_affix_dag(graph, start, direction, &mut visited)?;
                if usize::from(start.id()) > 1228465 && usize::from(start.id()) < 1228483 {
                    log::debug!("affix tree {:?}", shared_affix_dag);
                }
                res.extend(enumerate_shared_affix_subg(&shared_affix_dag, &graph)?);
            } else {
                log::debug!(
                    "skipping oriented visited node {}{}",
                    if start.is_reverse() { '<' } else { '>' },
                    usize::from(start.id())
                );
            }

            // process node in next iteration in reverse direction
            start = start.flip();
        }
    }

    Ok(res)
}

fn print<W: io::Write>(
    affixes: Vec<AffixSubgraph>,
    out: &mut io::BufWriter<W>,
) -> Result<(), io::Error> {
    for ics in affixes.iter() {
        let mut ends = Vec::new();
        for (v, direction, position) in ics.ends.iter() {
            ends.push(format!(
                "{}{}:{}",
                match direction {
                    Direction::Right => '>',
                    Direction::Left => '<',
                },
                v,
                position
            ));
        }
        writeln!(
            out,
            "{}{}\t{}\t{}\t{}",
            match ics.start.1 {
                Direction::Right => '>',
                Direction::Left => '<',
            },
            &ics.start.0,
            &ics.start.2,
            ends.join(","),
            &ics.sequence
        )?;
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
    let graph = HashGraph::from_gfa(&gfa);

    log::info!("identifying bubbles that multifurcate despite having identical sequences");
    log::info!("testing prefixes");
    writeln!(
        out,
        "{}",
        [
            "oriented_start_node",
            "startpos",
            "oriented_end_nodes",
            "shared_sequence"
        ]
        .join("\t")
    )?;
    if let Ok(prefixes) = find_shared_affixes(&graph, Direction::Right) {
        print(prefixes, &mut out)?;
    }
    log::info!("testing suffixes");
    if let Ok(suffixes) = find_shared_affixes(&graph, Direction::Left) {
        print(suffixes, &mut out)?;
    }

    log::info!("done");
    Ok(())
}
