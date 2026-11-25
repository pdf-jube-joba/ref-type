# Scaling benchmarks

[generators.py](generators.py) builds inputs whose dimensions can be varied independently.
[run.py](run.py) measures them with full checks and a fresh cache for each repetition.
Run from the repository root:

```sh
cargo build -p cli --release --locked
python3 benchmarks/bench.py scaling --binary target/release/cli --axes chain --sizes 8 16 32 64
```

| Axis | Dimension varied by `--sizes` |
| --- | --- |
| `chain` | Number of packages in a dependency chain |
| `consumers` | Number of packages importing a shared dependency |
| `width` | Number of declarations in a parameterized source module |
| `imports` | Number of module instantiations and imports |
| `locals` | Number of module instantiations in local contexts |
| `resident` | Number of independent declaration groups followed by reads of earlier type aliases |

`--axes` selects dimensions; the default is all six.
`--sizes` defaults to `16 32 64`, and `--runs` defaults to three repetitions.
`--width` fixes declarations per source module or package outside the `width` axis.
`--imports` fixes the import count for the `width` axis.
Both parameters default to 32.
`--resident-mib` sets the resident expression-page budget and defaults to 1 MiB.
The `resident` axis exercises restoration of earlier graph pages under that budget.

Reports default to `benchmarks/runs/scaling/report.json`.
Generated sources and caches are removed when the suite exits.
See the [shared options](../README.md) for resource limits, profiling, work directories, and reports.
