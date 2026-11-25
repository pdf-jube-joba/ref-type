# Resolver benchmarks

This directory contains the Rust measurement program, its Cargo manifest, fixed inputs, and [case definitions](cases.toml) for source loading and name resolution.
Input paths in the catalog are relative to this directory.

`nested-projections` measures consecutive field projections before type inference.
The input intentionally leaves type information unresolved; this case runs without type checking.

Run from the repository root:

```sh
cargo build -p ref-type-bench --locked
python3 benchmarks/bench.py case nested-projections --runs 3
```

The helper also accepts an arbitrary `.ref` file, package, or workspace:

```sh
target/debug/resolve-bench /path/to/input
```

It reports source-loading time, name-resolution time, and resolved module, declaration, and reference counts.
The Python runner additionally records total process time and resources, including startup and source loading.
`--binary` selects another prebuilt resolver executable, including a release build.
See the [shared options](../README.md) for resource limits, profiling, and reports.
