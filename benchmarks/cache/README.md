# Cache benchmarks

[scenarios.py](scenarios.py) generates small package graphs and measures cache reuse and invalidation in a shared temporary cache.
Run from the repository root:

```sh
cargo build -p cli --release --locked
python3 benchmarks/bench.py cache --binary target/release/cli --depth 8
```

The sequence records these conditions:

1. A cold dependency chain, an unchanged warm check, and a different consumer of the same dependencies.
2. An entry-source edit and a transitive dependency-source edit.
3. Cold and warm checks of a diamond dependency graph.
4. Reordering direct dependencies and adding an independent dependency.

`--depth` sets the number of intermediate packages between the base package and the chain consumer.
Each scenario records its own measurement in the report.
Generated packages and their shared cache are removed when the suite exits.
See the [shared options](../README.md) for resource limits, profiling, and reports.
