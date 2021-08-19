# GFAffix

GFAffix identifies walk-preserving shared affixes in variation graphs and collapses them into a non-redundant graph structure.

# Dependencies

`GFAffix` is written in RUST and requires a working RUST build system for
installation. See
[https://www.rust-lang.org/tools/install](https://www.rust-lang.org/tools/install)
for more details. 

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

## From bioconda channel

Make sure you have [ttps://conda.io](conda) installed!

```
conda install -c bioconda gfaffix
```

### From binary release (linux x86\_64)

```

wget --no-check-certificate -c https://github.com/marschall-lab/GFAffix/releases/download/0.1.2/GFAffix-0.1.2_linux_x86_64.tar.gz 
tar -xzvf GFAffix-0.1.2_linux_x86_64.tar.gz 

# you are ready to go! 
./GFAffix-0.1.2/gfaffix


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
gfaffix 0.1.2
Daniel Doerr <daniel.doerr@hhu.de>
Discover walk-preserving shared prefixes in multifurcations of a given graph.

    - Do you want log output? Call program with 'RUST_LOG=info gfaffix ...'
    - Log output not informative enough? Try 'RUST_LOG=debug gfaffix ...'

USAGE:
    gfaffix [FLAGS] [OPTIONS] <graph>

ARGS:
    <graph>    graph in GFA1 format

FLAGS:
    -c, --check_transformation    Verifies that the transformed parts of the graphs spell out the
                                  identical sequence as in the original graph. Only for debugging
                                  purposes.
    -h, --help                    Prints help information
    -V, --version                 Prints version information

OPTIONS:
    -x, --dont_collapse <no-collapse-path>
            Do not collapse nodes on a given paths ("P" lines) that match given regular expression
            [default:  ]

    -o, --output_refined <refined-graph-out>
            write refined graph in GFA1 format to supplied file [default:  ]

    -t, --output_transformation <transformation-out>
            report original nodes and their corresponding walks in refined graph to supplied file
            [default:  ]
```

## Execution

```
RUST_LOG=info gfaffix examples/example1.gfa -o example1.gfa -t example1.trans > example1.shared_affixes
```
