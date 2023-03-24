[![Rust Build](https://github.com/marschall-lab/GFAffix/actions/workflows/rust_build.yml/badge.svg)](https://github.com/marschall-lab/GFAffix/actions/workflows/rust_build.yml) [![Anaconda-Server Badge](https://anaconda.org/bioconda/gfaffix/badges/version.svg)](https://conda.anaconda.org/bioconda) [![Anaconda-Server Badge](https://anaconda.org/bioconda/gfaffix/badges/platforms.svg)](https://anaconda.org/bioconda/gfaffix) [![Anaconda-Server Badge](https://anaconda.org/bioconda/gfaffix/badges/license.svg)](https://anaconda.org/bioconda/gfaffix)

# GFAffix

![GFAffix collapses walk-preserving shared affixes](doc/gfaffix-illustration.png?raw=true "GFAffix collapses walk-preserving shared affixes")

GFAffix identifies walk-preserving shared affixes in variation graphs and collapses them into a non-redundant graph structure.

# Dependencies

`GFAffix` is written in RUST and requires a working RUST build system for installation. See [https://www.rust-lang.org/tools/install](https://www.rust-lang.org/tools/install) for more details. 

It makes use of the following crates:
* clap
* env\_logger
* gfa
* handlegraph
* log
* quick-csv
* regex
* rustc-hash

## Installation

### From bioconda channel

Make sure you have [conda](https://conda.io) installed!

```
conda install -c bioconda gfaffix
```

### From binary release (linux x86\_64)

```

wget --no-check-certificate -c https://github.com/marschall-lab/GFAffix/releases/download/0.1.4/GFAffix-0.1.4_linux_x86_64.tar.gz 
tar -xzvf GFAffix-0.1.4_linux_x86_64.tar.gz 

# you are ready to go! 
./GFAffix-0.1.4/gfaffix


```

### From repository

```
# install GFAffix
git clone https://github.com/marschall-lab/GFAffix.git
# build program
cargo build --manifest-path GFAffix/Cargo.toml --release
```

## Command Line Interface

```
$ gfaffix --help
gfaffix 0.1.4b
Daniel Doerr <daniel.doerr@hhu.de>
Discover walk-preserving shared prefixes in multifurcations of a given graph.

    - Do you want log output? Call program with 'RUST_LOG=info gfaffix ...'
    - Log output not informative enough? Try 'RUST_LOG=debug gfaffix ...'

USAGE:
    gfaffix [OPTIONS] <GRAPH>

ARGS:
    <GRAPH>    graph in GFA1 format

OPTIONS:
    -c, --check_transformation
            Verifies that the transformed parts of the graphs spell out the identical sequence as in
            the original graph. Only for debugging purposes

    -h, --help
            Print help information

    -o, --output_refined <REFINED_GRAPH_OUT>
            Write refined graph in GFA1 format to supplied file [default: " "]

    -t, --output_transformation <TRANSFORMATION_OUT>
            Report original nodes and their corresponding walks in refined graph to supplied file
            [default: " "]

    -V, --version
            Print version information

    -x, --dont_collapse <NO_COLLAPSE_PATH>
            Do not collapse nodes on a given paths ("P" lines) that match given regular expression
            [default: " "]
```

## Execution

```
RUST_LOG=info gfaffix examples/example1.gfa -o example1.gfa -t example1.trans > example1.shared_affixes
```
