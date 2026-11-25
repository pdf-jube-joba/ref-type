# Benchmarks

The Python entry point is `bench.py`, using Linux and the Python 3.11+ standard library.
Build measured binaries beforehand; measurements run sequentially.
The Rust helper belongs to the root Cargo workspace and shares its lockfile, dependency versions, profiles, and target directory.
Default Cargo commands build the implementation crates; `--workspace` also includes the benchmark helper.

## Dependencies and responsibilities

| File | Responsibility | Local dependencies |
| --- | --- | --- |
| `bench.py` | Named cases, explicit inputs, and cache scenarios | `measurements`, `log_analysis`, `workloads` |
| `large_scale.py` | Measurements across generated workload dimensions | `measurements`, `workloads` |
| `measurements.py` | Process supervision, resource accounting, and atomic reports | `log_analysis`, `workloads` |
| `log_analysis.py` | Parse timing, progress, and cost logs | Standard library |
| `workloads.py` | Package discovery, source digests, and input generation | Standard library |
| `tools/resolve.rs` | Resolver measurements without type checking | `project`, `resolve`, `timing` |

Reusable modules do not import command entry points.
The benchmark tools run prebuilt implementation binaries independently of the acceptance runner.
Binary defaults honor `CARGO_TARGET_DIR`.

## Selecting cases

[cases.toml](cases.toml) lists each case's purpose, input, measurement target, and default resource limits.
CLI options can override resource limits.

```sh
python3 benchmarks/bench.py list
cargo build -p cli --release --locked
python3 benchmarks/bench.py case shared-bodies --binary target/release/cli --runs 3

cargo build -p ref-type-bench --locked
python3 benchmarks/bench.py case nested-projections
python3 -m unittest discover -s benchmarks -v
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
python3 benchmarks/bench.py libraries /path/to/package --binary target/release/cli
python3 benchmarks/large_scale.py --binary target/release/cli --axes chain --sizes 8 16 32 64
python3 benchmarks/large_scale.py --binary target/release/cli --sizes 16 32 64 --runs 3
```

`libraries` requires explicit package or workspace paths and enumerates their dependencies.
Packages reached through multiple dependency paths are measured only once.

`cache` measures unchanged checks, a different consumer, entry edits, transitive dependency edits, dependency-order changes, and independent dependency additions in sequence.

`large_scale.py` independently scales dependency chains, consumers of shared dependencies, namespace width, import counts, imports in local contexts, and independent declaration groups.
`--axes` selects dimensions; `--resident-mib` sets the resident expression-page budget.
It performs full checks with a fresh cache per repetition; `--width` fixes declarations per package while `--axes chain` varies dependency depth.
The independent-group workload reads old type aliases after creating the groups, exercising graph page restoration.

`resolve-bench PATH` measures source loading and name resolution without type checking.
Use it separately from end-to-end CLI measurements.
Cache publication failures and checkpoint recovery are covered by the CLI integration tests:

```sh
cargo test -p cli --test implementation --locked
```

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
| `--cache-mib` | Unlimited if omitted; CLI cache budget |
| `--output-mib` | 8 MiB; log size limit per run |
| `--progress-seconds` | 30 seconds; elapsed-time reporting interval |

On interruption or limit exhaustion, the supervisor is notified to exit; child processes are awaited and forcibly terminated if necessary.
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
The CLI uses Rust's standard allocator; external allocation profilers can observe its ordinary heap allocations.
