[![Rust Build](https://github.com/marschall-lab/GFAffix/actions/workflows/rust_build.yml/badge.svg)](https://github.com/marschall-lab/GFAffix/actions/workflows/rust_build.yml) [![Anaconda-Server Badge](https://anaconda.org/bioconda/gfaffix/badges/version.svg)](https://conda.anaconda.org/bioconda) [![Anaconda-Server Badge](https://anaconda.org/bioconda/gfaffix/badges/platforms.svg)](https://anaconda.org/bioconda/gfaffix) [![Anaconda-Server Badge](https://anaconda.org/bioconda/gfaffix/badges/license.svg)](https://anaconda.org/bioconda/gfaffix)

# GFAffix

![GFAffix collapses walk-preserving shared affixes](doc/gfaffix-illustration.png?raw=true "GFAffix collapses walk-preserving shared affixes")

GFAffix identifies walk-preserving shared affixes in variation graphs and collapses them into a non-redundant graph structure.

# Dependencies

`GFAffix` is written in RUST and requires a working RUST build system for installation. See [https://www.rust-lang.org/tools/install](https://www.rust-lang.org/tools/install) for more details. 

It makes use of the following crates:
* clap
* env\_logger
* flate2
* gfa
* handlegraph
* indexmap
* log
* rayon
* regex
* rustc-hash

## Installation

### From bioconda channel

Make sure you have [conda](https://conda.io)/[mamba](https://anaconda.org/conda-forge/mamba) installed!

```
mamba install -c conda-forge -c bioconda gfaffix
```

### From binary release

#### Linux x86\_64

```
wget --no-check-certificate -c https://github.com/marschall-lab/GFAffix/releases/download/0.2.0/GFAffix-0.2.0_linux_x86_64.tar.gz 
tar -xzvf GFAffix-0.2.0_linux_x86_64.tar.gz 

# you are ready to go! 
./GFAffix-0.2.0_linux_x86_64/gfaffix
```

#### MacOS X arm64

```
wget --no-check-certificate -c https://github.com/marschall-lab/GFAffix/releases/download/0.2.0/GFAffix-0.2.0_macos_x_arm64.tar.gz 
tar -xzvf GFAffix-0.2.0_macos_x_arm64.tar.gz 

# you are ready to go! 
./GFAffix-0.2.0_macos_x_arm64/gfaffix
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
Discover and collapse walk-preserving shared affixes of a given variation graph.

Usage: gfaffix [OPTIONS] <GRAPH>

Arguments:
  <GRAPH>  graph in GFA1 format, supports compressed (.gz) input

Options:
  -o, --output_refined <REFINED_GRAPH_OUT>
          Write refined graph output (GFA1 format) to supplied file instead of stdout; if file name
          ends with .gz, output will be compressed [default: ]
  -t, --output_transformation <TRANSFORMATION_OUT>
          Report original nodes and their corresponding walks in refined graph to supplied file
          [default: ]
  -c, --check_transformation
          Verifies that the transformed parts of the graphs spell out the identical sequence as in the
          original graph
  -a, --output_affixes <AFFIXES_OUT>
          Report identified affixes [default: ]
  -x, --dont_collapse <NO_COLLAPSE_PATH>
          Do not collapse nodes on a given paths/walks ("P"/"W" lines) that match given regular
          expression [default: ]
  -p, --threads <THREADS>
          Run in parallel on N threads [default: 1]
  -v, --verbose
          Sets log level to debug
  -h, --help
          Print help
  -V, --version
          Print version
```

## Execution

```
gfaffix examples/example1.gfa -o example1.gfa > example1.gfaffixed.gfa
```
