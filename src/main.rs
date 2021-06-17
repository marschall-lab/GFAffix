/* standard use */
use rustc_hash::FxHashMap;
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
    pub start: Handle,
    pub ends: Vec<Handle>,
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
        let mut parents : Vec<Handle> = graph.neighbors(u, Direction::Left).collect();
        parents.sort();
        // insert child in variant-preserving data structure
        branch.entry((seq[0], parents)).or_insert(Vec::new()).push(u);
    }

    for children in branch.values() {
        if children.len() > 1 {
            res.push(AffixSubgraph { sequence : get_shared_prefix(children, graph)?, start : v, ends : children.clone()});
        }
    }
     
    Ok(res)
}


fn get_shared_prefix(nodes: &Vec<Handle>, graph: &HashGraph) -> Result<String, std::string::FromUtf8Error> {
    let mut seq: Vec<u8> = Vec::new();
    
    let sequences : Vec<Vec<u8>> = nodes.iter().map(|v| graph.sequence_vec(*v)).collect();

    let mut i = 0;
    while sequences[0].len() > i {
        let c : u8 = sequences[0][i];
        if sequences.iter().any(|other| other.len() <= i || other[i] != c) {
            break
        }
        seq.push(c);
        i += 1;
    }

    String::from_utf8(seq)
}


fn find_and_report_variant_preserving_shared_affixes<W: Write>(graph: &HashGraph, out: &mut io::BufWriter<W>) -> Result<(), Box<dyn Error>> {
    
    for mut v in graph.handles() {
        for _ in 0..2 {
            log::debug!(
                "processing oriented node {}{}",
                if v.is_reverse() { '<' } else { '>' },
                usize::from(v.id())
            );

            // process node in forward direction
            // make sure each multifurcation is tested only once
            let affixes =
                enumerate_variant_preserving_shared_affixes(graph, v)?;
            for affix in affixes.iter() {
                print(affix, out)?;
            }

            // process node in next iteration in reverse direction
            v= v.flip();
        }
    }

    Ok(())
}

fn print<W: io::Write>(
    affix: &AffixSubgraph,
    out: &mut io::BufWriter<W>,
) -> Result<(), io::Error> {
    let ends : Vec<String> = affix.ends.iter().map(|&v| format!(
            "{}{}",
            if v.is_reverse() {'<'} else { '>' },
            usize::from(v.id()),
        )).collect();
    writeln!(
        out,
        "{}{}\t{}\t{}",
        if affix.start.is_reverse() {'<'} else { '>' },
        usize::from(affix.start.id()),
        ends.join(","),
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
    let graph = HashGraph::from_gfa(&gfa);

    log::info!("identifying bubbles that multifurcate despite having identical sequences");
    writeln!(
        out,
        "{}",
        [
            "oriented_start_node",
            "oriented_end_nodes",
            "shared_sequence",
        ]
        .join("\t")
    )?;
    if let Err(e) = find_and_report_variant_preserving_shared_affixes(&graph, &mut out) {
        panic!("gfaffix failed: {}", e);
    }
    out.flush()?;
    log::info!("done");
    Ok(())
}
