use handlegraph::handle::Handle;

// structure for storing reported subgraph

#[derive(Clone, Debug)]
pub struct AffixSubgraph {
    pub sequence: String,
    pub parents: Vec<Handle>,
    pub shared_prefix_nodes: Vec<Handle>,
}
