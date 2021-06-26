# GFAffix

## How to get started

```
$ git clone https://github.com/danydoerr/GFAffix.git
$ cargo build --manifest-path GFAffix/Cargo.toml --release
$ ./GFAffix/target/release/gfaffix --help
gfaffix 0.1
Daniel Doerr <daniel.doerr@hhu.de>
Discover path-preserving shared prefixes in multifurcations of a given graph.

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
    -o, --output_refined <refined-graph-out>
            write refined graph in GFA1 format to supplied file [default:  ]

    -t, --output_transformation <transformation-out>
            report original nodes and their corresponding paths in refined graph to supplied file
            [default:  ]
```


