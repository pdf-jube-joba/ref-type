# Scaling benchmarks

[generators.py](generators.py) builds inputs whose dimensions can be varied independently.
[run.py](run.py) measures them with a fresh cache for each repetition. The default axes force full checks.
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
| `checkpoint-disk` | Number of independent workspace packages with 32 declaration groups each |
| `layered` | Width of each of two middle layers in an `A → B → C → D` workspace graph |

`--axes` selects dimensions; the default is the original six axes. The two workspace axes are opt-in.
`--sizes` defaults to `16 32 64`, and `--runs` defaults to three repetitions.
`--width` fixes declarations per source module or package outside the `width` axis.
`--imports` fixes the import count for the `width` axis.
Both parameters default to 32.
`--resident-mib` sets the resident expression-page budget and defaults to 1 MiB.
The `resident` axis exercises restoration of earlier graph pages under that budget.

Both workspace axes pass the workspace directory once to the ordinary checker. They sample allocated cache bytes about every 0.5 seconds, including checker staging directories and deduplicating hard links. `cache_peak_allocated_bytes` is the greatest observed sample (and can miss shorter spikes); `cache_final_allocated_bytes` is measured after exit. Sampling itself adds work, so compare timings only with identical sampling conditions.

```sh
python3 benchmarks/bench.py scaling --binary target/release/cli --axes checkpoint-disk --sizes 16 --width 6 --runs 1 --extra --checkpoint-seconds 0
python3 benchmarks/bench.py scaling --binary target/release/cli --axes layered --sizes 10 --width 6 --runs 1
```

The first command stresses checkpoint replacement by saving at every eligible module boundary. The second makes 22 packages: each `B` imports `A`, each `C` imports every `B`, and `D` imports every `C`. The source terms use all those imports.

Reports default to `benchmarks/runs/scaling/report.json`.
Generated sources and caches are removed when the suite exits.
See the [shared options](../README.md) for resource limits, profiling, work directories, and reports.
