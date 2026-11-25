# Benchmarks

The Python entry point is `bench.py`, using Linux and the Python 3.11+ standard library.
Build measured binaries beforehand; measurements run sequentially.

## Selecting cases

[cases.toml](cases.toml) lists each case's purpose, input, measurement target, and default resource limits.
CLI options can override resource limits.

```sh
python3 benchmarks/bench.py list
cargo build -p cli --release --locked
python3 benchmarks/bench.py case shared-bodies --binary target/release/cli --runs 3

cargo build --manifest-path benchmarks/Cargo.toml --bin resolve-bench --locked
python3 benchmarks/bench.py case nested-projections
python3 benchmarks/tests.py
```

## Other inputs and generated workloads

| Subcommand | Purpose |
| --- | --- |
| `run PATH...` | Repeated measurements of specified inputs |
| `libraries PATH...` | Measure package or workspace dependencies first |
| `cache` | Generated workloads covering chains, diamonds, edits, and dependency-order changes |
| `analyze LOG` | Analyze completed and interrupted logs |

```sh
python3 benchmarks/bench.py cache --binary target/release/cli --depth 8
python3 benchmarks/bench.py run benchmarks/inputs/shared-bodies.ref --runs 3
python3 benchmarks/bench.py libraries libs/category --binary target/release/cli
python3 benchmarks/scaling.py --binary target/release/cli --depths 8 16 32 64
python3 benchmarks/large_scale.py --binary target/release/cli --sizes 16 32 64 --runs 3
python3 benchmarks/heap_spill.py --binary target/release/cli --memory-mib 32
```

Without inputs, `libraries` enumerates packages in `libs/ref.toml` and their dependencies.
Packages reached through multiple dependency paths are measured only once.

`cache` measures unchanged checks, a different consumer, entry edits, transitive dependency edits, dependency-order changes, and independent dependency additions in sequence.
It also checks diagnostics for an unusable checkpoint destination and checking after the destination is repaired.
`--checkpoint` adds interruption after a save report, resumption, unchanged checks, and automatic recovery from forced worker termination.

`scaling.py` varies only dependency-chain depth while keeping declarations per package fixed, measuring from an empty cache.
`--width` selects declarations per package; `--force` passes `--full-check`.

`large_scale.py` independently scales dependency chains, consumers of shared dependencies, namespace width, import counts, imports in local contexts, and independent declaration groups.
`--axes` selects dimensions; `--resident-mib` sets the resident expression-page budget.

`large_scale_suite.py` runs three individual-selection measurements, full checks at 3072 / 8192 MiB, reuse, scaling, and recovery in sequence.
`--baseline` adds the same individual selections and full checks of the old approach with a 600-second limit.
Provide prebuilt binaries; `--stages` selects stages, and `--packages` selects inputs for full checks and reuse.

```sh
python3 benchmarks/large_scale_suite.py --binary target/debug/cli --baseline benchmarks/runs/baseline-cli
```

`resolve-bench PATH --retention` resolves names per package and simulates releasing checked inputs to measure resolver retention.
It separates measurements with source syntax trees retained and released, reporting RSS and virtual memory on Linux.
It uses the system allocator and returns unused pages before observation on GNU systems.
This mode does not type-check; use it separately from end-to-end CLI measurements.

## Output and caches

Reports default to `runs/<case-name>/report.json` for named cases and `runs/<subcommand>/report.json` for other measurements.
`--output` selects the report path; run logs and CLI reports are stored in an adjacent `<name>-logs/` directory.
Comparison JSON, run conditions, and analysis also belong in `runs/`.

`run` and `case` default to `--cache-mode off`, passing `--no-cache` to the CLI for checker measurements.
`--cache-mode cold` creates an empty temporary cache per run and includes persistence in the measurement.
`--cache-mode shared` shares `cache/` beside the report across runs; `--cache-dir` selects another location.
`libraries` uses a shared cache by default.
Temporary sources and caches are created in `runs/scratch/` and removed on exit.
`--work-dir` selects the temporary directory.

JSON is updated atomically after each run, preserving results up to interruption.
It records wall time, user time, system time, peak RSS, exit status, source digests, storage size, and acceptance/reuse from public reports.
Successful measurements are summarized by input with median times and peak RSS.
Measurements whose sources or binaries change during execution are not considered complete.

## Resource limits and detailed analysis

| Option | Default and purpose outside named cases |
| --- | --- |
| `--seconds` | 300 seconds; time limit per run |
| `--memory-mib` | 3072 MiB; checker resident-memory paging target |
| `--cache-mib` | Unlimited if omitted; CLI cache budget |
| `--output-mib` | 8 MiB; log size limit per run |
| `--batch-seconds` | Seconds before splitting the checking scope, passed to an old CLI for comparison |
| `--progress-seconds` | 30 seconds; elapsed-time reporting interval |

On interruption or limit exhaustion, the supervisor is notified to exit; child processes are awaited and forcibly terminated if necessary.
The memory setting specifies the CLI paging target; automatic paging is managed by the CLI and OS.
Peak RSS is the largest individual-process value returned by `wait4`, including descendants.
It is not the sum of memory across all processes at a single instant.

```sh
python3 benchmarks/bench.py case shared-bodies --profile-costs --profile-phases
python3 benchmarks/bench.py analyze benchmarks/runs/shared-bodies/report-logs/000-shared-bodies.log
```

`--profile-costs` and `--profile-phases` aggregate call counts and timings across workers and record phase order.
`REF_TYPE_PROFILE_*` environment variables are also supported.
`analyze` reports active declarations, completed declaration/module timings, phase elapsed times, and cost summaries.
Detailed profiling adds overhead, so measure it separately from ordinary repetitions.

Use `--command` for another program.
Only input paths are appended to the command; supply additional arguments after the final `--extra` option.
Use [alloc_trace.c](tools/alloc_trace.c) to trace large allocations.
