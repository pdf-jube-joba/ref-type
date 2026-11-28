# Benchmarks

The Python entry point is `bench.py`, using Linux and the Python 3.11+ standard library.
Build measured binaries beforehand; measurements run sequentially.
The Rust helper in `resolver/` belongs to the root Cargo workspace and shares its lockfile, dependency versions, profiles, and target directory.
Default Cargo commands build the implementation crates; `--workspace` also includes the benchmark helper.

## Benchmark groups

| Directory | Purpose | Main files |
| --- | --- | --- |
| [checker/](checker/README.md) | End-to-end checker measurements | `cases.toml`, `.ref` inputs |
| [resolver/](resolver/README.md) | Source loading and name resolution | `Cargo.toml`, `resolve.rs`, `cases.toml`, `.ref` inputs |
| [cache/](cache/README.md) | Cache reuse and invalidation scenarios | `scenarios.py` |
| [workloads/](workloads/README.md) | Standalone checker workloads derived from focused library profiles | `run.py`, `generators.py` |
| [scaling/](scaling/README.md) | Measurements across generated workload dimensions | `run.py`, `generators.py` |
| `common/` | Process supervision, reports, log analysis, and source/package helpers | `measurements.py`, `log_analysis.py`, `sources.py` |
| `tests/` | Small regression tests for the benchmark tools | `test_bench.py` |
| `runs/` | Generated reports, logs, caches, and temporary inputs | Created during measurements |

`bench.py` selects and dispatches measurements and log analysis.
Reusable modules in `common/` do not import benchmark groups or the command entry point.
The benchmark tools run prebuilt implementation binaries independently of the acceptance runner.
Binary defaults honor `CARGO_TARGET_DIR`.

## Relationship to the implementation

The [source acceptance suite](../tests/README.md#compatibility-contract) defines an external language contract using ordinary input-path invocations and acceptance/rejection exit codes.
Benchmarks investigate the performance of the current implementation.

End-to-end checker inputs provide comparison points across implementation changes; prefer retaining the same inputs and recording comparable run conditions.
Internal APIs used by the resolver helper, profiling labels, resource counters, and expression-page budgets describe the current architecture.
When that architecture changes, update, replace, or retire the affected helpers and internal measurements alongside the implementation.
These tools must not require preserving an internal representation or operation count.

Use timing, memory, and storage results to investigate performance regressions.
The benchmark tool's regression tests protect reliable execution and reporting; measured performance and internal counters are not correctness assertions.

## Selecting cases

[checker/cases.toml](checker/cases.toml) and [resolver/cases.toml](resolver/cases.toml) list each case's purpose, input, and default time limit.
Input paths are relative to their catalog's directory; that directory also determines the measurement target.
Case names must be unique across both catalogs.
CLI options can override resource limits.
`--binary` selects the measured executable for both checker and resolver cases.
Without it, checker cases use `debug/cli` and resolver cases use `debug/resolve-bench` under the Cargo target directory.
`--command` takes precedence over `--binary`.

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
| `workloads` | Quick and stress presets for proof terms, Program terms, macro expansion and focused file checks |
| `scaling` | Generated workloads with varying dependency depth, declaration counts, imports, and resident budgets |
| `analyze LOG` | Analyze completed and interrupted logs |

```sh
python3 benchmarks/bench.py workloads --binary target/release/cli
python3 benchmarks/bench.py cache --binary target/release/cli --depth 8
python3 benchmarks/bench.py run benchmarks/checker/shared-bodies.ref --runs 3
python3 benchmarks/bench.py libraries /path/to/package --binary target/release/cli
python3 benchmarks/bench.py scaling --binary target/release/cli --axes chain --sizes 8 16 32 64
python3 benchmarks/bench.py scaling --binary target/release/cli --sizes 16 32 64 --runs 3
```

`libraries` requires explicit package or workspace paths and enumerates their dependencies.
Packages reached through multiple dependency paths are measured only once.

`cache` runs the scenarios in [cache/scenarios.py](cache/scenarios.py).
See [cache/](cache/README.md) for their order and shared-cache conditions.

`scaling` uses [scaling/run.py](scaling/run.py) and [scaling/generators.py](scaling/generators.py).
See [scaling/](scaling/README.md) for dimensions and generation parameters.

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
`runs/` is ignored by Git and can be deleted between measurements.
The next measurement creates its output directories and new results; deleted historical results are not restored.

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
Source digests include the selected entry and its external modules, plus package, workspace, and dependency manifests and sources when measuring a directory.
Paths in the digest are relative to the input directory or the entry file's parent, so relocating an unchanged input tree preserves its digest.
Unreferenced source files are excluded.

## Resource limits and detailed analysis

| Option | Default and purpose outside named cases |
| --- | --- |
| `--seconds` | 300 seconds; time limit per run |
| `--cache-mib` | Unlimited if omitted; CLI cache budget |
| `--output-mib` | 8 MiB; log size limit per run |
| `--progress-seconds` | 30 seconds; elapsed-time reporting interval |

On interruption or limit exhaustion, the supervisor is notified to exit; child processes are awaited and forcibly terminated if necessary.
The runner adopts orphaned descendants and terminates remaining processes in the measured session after a two-second grace period, including separate process groups.
A command that exits while descendants remain is recorded as `unfinished_children` and is not considered complete.
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
