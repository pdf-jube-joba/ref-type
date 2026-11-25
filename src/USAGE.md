# Usage

Run commands from the repository root.

```sh
cargo run -p cli -- /path/to/package
cargo run -p cli -- /path/to/workspace
cargo run -p cli -- /path/to/package --module example.Main --diagnostics compact
```

Inputs are package or workspace directories, or `.ref` files containing a root module.
A package's entry point is `src/root.ref`; dependencies are specified in `ref.toml`.

```toml
[package]
name = "example"
[dependencies]
std = { path = "../std" }
```

A shared parent directory can define a workspace.

```toml
[workspace]
packages = ["std", "example"]
```

A workspace input checks all members and their dependencies, including the root package if `[package]` is also present.
To select one member, pass its directory as input or its package name to `--module`.
See [surface syntax](../docs/language/syntax.md#2-modules) for external modules and imports, and [libs](https://github.com/pdf-jube-joba/ref-type-libs/tree/main/libs) for library layout.

## Checking and caching

Workspace members share `refcache/` directly under the workspace, even when invoked through a source file.
Outside a workspace, caches are stored in the input directory, or the parent directory for a single file.
`--cache-dir` overrides these defaults.

| Option | Behavior |
| --- | --- |
| `--module NAME` | Check the specified module, its children, and declarations they reference |
| `--module-only` | Check the module selected by `--module` itself and its references |
| `--list-modules` | Print source module checking paths, one per line |
| `--time-limit-seconds N` | Total Linux package-checking time limit; unlimited if omitted |
| `--parse-only` | Parse sources and load external modules and packages |
| `--save-source-snapshot PATH` | Save loaded sources and their original file identities as JSON |
| `--source-snapshot PATH` | Check sources from saved JSON |
| `--no-cache` | Check the selected scope without reading or writing the persistent cache |
| `--full-check` | Recheck the selected scope and update the cache with verified results |
| `--full-check-local` | Recheck the selected scope of the entry package or each workspace package while reusing cached external dependencies |
| `--no-progress` | Hide the progress bar and timings |
| `--progress-tty` | Show progress on the controlling terminal (`/dev/tty`) separately from log output |
| `--cache-dir PATH` | Change the cache directory |
| `--cache-budget-mib N` | Disk retention budget in MiB; unlimited if omitted; artifacts in use are protected |
| `--clear-cache` | Clear the cache directory before processing |
| `--cache-stats` | Print parse, check, reuse, and save counts |
| `--report-json PATH` | Save acceptance, checking/storage statistics, worker/recovery counts, CPU time, and peak RSS/virtual memory as JSON |
| `--checkpoint-seconds N` | Mid-package checkpoint interval; default: 30 seconds; 0 saves at every module completion |
| `--stats` | Print raw / kernel node counts and other statistics |
| `--trace` | Perform verification and print type-checking, registration, and reduction logs |
| `--diagnostics compact` / `detailed` | Select diagnostic detail |

The JSON `execution` section distinguishes duplicate source checks (`duplicate_source_steps`), recovery replays (`replayed_source_steps`), and unsaved work (`lost_steps`).
Interruption, time-limit termination, and termination due to OS memory exhaustion or an external SIGKILL are recorded as `interrupted`, `time-limit`, and `memory-limit`, respectively.
`last_module` and `last_checkpoint` identify the position reached on abnormal exit.

Without `--module`, all modules in the entry point and loaded dependencies are checked.
With it, checking is limited to that module, its children, and their references.
`--module-only` limits checking to the module itself and its references; duplicate module names are distinguished by paths such as `Name#2` from `--list-modules`.
`--full-check-local` does not change the scope; it forces rechecking of the entry package or workspace members.
Normal checks also verify dependencies' current contents.

On Linux, one worker retains the package-checking session while a supervisor monitors resources and progress.
The worker shares verified dependency declarations and namespaces and persists or spills expression graphs page by page.
Expression pages evicted from RAM are written directly to `refcache/objects/` through the same store used by checkpoints.
They use the store's checksums, leases, and garbage collection and are loaded again when needed.
The expression-page RAM budget defaults to 128 MiB and is configurable with `REF_TYPE_GRAPH_RESIDENT_MIB`.
This budget covers expression pages; it is not a limit on the process's total RAM.
The CLI uses Rust's standard allocator.
After abnormal termination, the same request resumes if a new checkpoint has been published.
Published checkpoints are transferred to normal storage even on interruption.
Explicit total time limits and user interruptions do not trigger automatic resumption.
The source snapshot is fixed during execution; source changes require another run.
The report's `source_steps` counts completed source-checking steps, `duplicate_source_steps` counts repeated checks within the run, and `lost_steps` counts progress beyond the checkpoint lost during recovery.
Index size, resident page size, and spill volume in `checking.session.graph` are recorded separately from OS RSS and virtual memory.

The [CLI integration tests](cli/tests/implementation.rs) cover cache publication failures and checkpoint recovery.
The [graph-store test](sema/src/graph_store.rs) checks that evicted pages use `refcache` and survive cache collection.

To check a saved version while continuing to edit, explicitly use a snapshot.
Saved file identities and contents fix the check without copying sources to another directory, allowing unchanged dependency caches to be reused.

```sh
mkdir -p work
cargo run -p cli -- /path/to/package --parse-only --save-source-snapshot work/source.json
cargo run -p cli -- /path/to/package --source-snapshot work/source.json --module example.Main
```

Use the same input location as when the snapshot was saved.
Diagnostics refer to saved sources; if the input JSON changes during checking, another run is required.
Normal checks continue to detect source changes during execution.

Cache matching includes the implementation, configuration, sources, manifests, dependency inputs, and checking scope.
Unchanged results are reused; dependency environments are restored for later package checks.
Checking can resume from checkpoints at module-completion boundaries.
Save-cost-based waiting is capped by the interval specified by `--checkpoint-seconds`.
`--full-check` and entry-point `--full-check-local` recheck forced scopes without carrying over results from past verification generations.
Recovery within the same run uses checkpoints saved in that generation.
`--full-check` starts a new generation without reusing saved verification results and shares declarations completed in that run with later requests.
When the budget is exceeded, artifacts in use and their dependencies are protected while unused artifacts are collected.
See [sema](sema/README.md#reuse) for storage formats and APIs.

`--cache-stats` prints query, I/O, compression, restoration, save-failure, and collection statistics.
`environment_hits` counts environment restorations, `restored_modules` counts modules skipped through restoration, and `package_hits` counts package artifact reuse.
`checkpoint_hits`, `checkpoint_writes`, and `checkpoint_skips` describe intermediate resumption; `budget_excess_bytes` reports budget excess due to data in use.
While `retained_bytes_is_upper_bound` is set, retention is a conservative cumulative value; GC updates it to the actual size.

The terminal shows progress, completion counts, the current module, elapsed time, and per-package `check` / `skip` counts.
Totals count source modules in the selected scope and dependencies, including cache-skipped modules as complete.
When redirected or logging is enabled, per-module timings go to stderr; `--progress-tty` can also show progress on the controlling terminal.
Each module's time includes its own parsing, expansion, checking, and saving; children and dependencies are counted separately.
`shared = total - sum of module times` includes shared preparation, checkpointing, cleanup, and similar work.
`total` measures CLI processing time, excluding Cargo build and startup time.

## Diagnostics and profiling

Diagnostics and logs go to stderr; query results go to stdout.
Diagnostics show locations, local contexts, required types, and constraints; `#0` denotes the innermost binding.
`_` is an inference hole, names such as `_0` share a hole within a declaration, and `?` is an inspection goal that returns failure even when solved.
Compact diagnostics stop at the first error.

```sh
RUST_LOG=ref_type::typing=debug cargo run -p cli -- /path/to/package --full-check
RUST_LOG=ref_type::reduction=trace cargo run -p cli -- /path/to/package --full-check
REF_TYPE_PROFILE_DECLARATIONS=1 cargo run -p cli -- /path/to/package --no-cache
```

`RUST_LOG` overrides the default `--trace` filter.

| Environment variable | Measurement |
| --- | --- |
| `REF_TYPE_PROFILE_DECLARATIONS` | Declaration checking time |
| `REF_TYPE_PROFILE_LOCAL_DEFINITIONS` | Local definition checking time |
| `REF_TYPE_PROFILE_LOWERING` | Kernel definition conversion and registration time |
| `REF_TYPE_PROFILE_CONVERSION=1` | Comparison counts, inputs, and current terms for long-running type-convertibility checks |
| `REF_TYPE_PROFILE_PHASES=1` | Time and RSS for each phase |
| `REF_TYPE_PROFILE_STORAGE=1` | Retention and I/O for checking steps, declaration cells, substitution tables, and expression pages |
| `REF_TYPE_GRAPH_RESIDENT_MIB=N` | Resident expression-page budget; native default: 128 MiB; minimum: 1 MiB |
| `REF_TYPE_PROFILE_MODULES=1` | Module loading, instantiation, and recovery |
| `REF_TYPE_PROFILE_PROGRESS=1` | Live phases, module start/completion, completion counts, and elapsed seconds |
| `REF_TYPE_PROFILE_NAMESPACES=1` | Import namespace and ID mapping counts |
| `REF_TYPE_DEBUG_HIR_IMPORTS=1` | Module IDs, arguments, and instantiation mappings before and after imports |
| `REF_TYPE_PROFILE_DIAGNOSTICS=1` | Diagnostic generation/display time and RSS |
| `REF_TYPE_PROFILE_ENVIRONMENTS=1` | Checkpoint keys, restoration positions, and saved sizes |
| `REF_TYPE_PROFILE_COSTS=1` | Inclusive/exclusive timings and cache statistics for nested operations |
| `REF_TYPE_PROFILE_COSTS_PROGRESS_MS=15000` | Progress reporting interval during cost profiling |

For the first three variables, `1` selects all entries; a name substring narrows the selection.
`REF_TYPE_COMPACT_DIAGNOSTICS=1` also selects compact diagnostics, but CLI settings take precedence.
`REF_TYPE_PROFILE_COSTS` can also filter by prefixes such as `resolve.,namespace.,kernel.`.
`inclusive_us` includes children; `exclusive_us` subtracts measured child time.
Compare recursive work using `cost_group` exclusive time.

`resolve.total` / `resolve.package` measure name resolution and expansion; `namespace.*` measures instantiation and reuse decisions.
`namespace.translation-failed.*` counts conversion failures during comparison; the first cause appears as `translation-failure sample=...`.
`query.environment-plan` measures checkpoint-key construction from checking order and dependency information.

In progress logs, `event=start` marks the start; `completed` and `package_completed` are completion counts.
The `module_seconds` value for `event=complete` is an intermediate cumulative value, unlike final totals that include end-of-run analysis collection and saving.
Checkpoint saves emit `event=checkpoint-saved`.

Use [benchmarks](../benchmarks/README.md) for detailed profiling, resource limits, and interrupted-log analysis.

```sh
cargo build -p cli --locked
REF_TYPE_PROFILE_PROGRESS=1 REF_TYPE_PROFILE_DECLARATIONS=1 \
  python3 benchmarks/bench.py run /path/to/package \
  --cache-mode cold --seconds 180 --progress-seconds 15 \
  --output benchmarks/runs/check/report.json
```

`--cache-mode cold` creates an empty dedicated cache and includes persistence in the measurement.
Peak RSS is the maximum for an individual process, including descendants.

## Implementation tests

```sh
cargo build -p cli --locked
python3 tests/tests.py
python3 -m unittest discover -s tests -v
python3 -m unittest discover -s benchmarks -v
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

The [acceptance tests](../tests/README.md) check Markdown sources and edit sequences for acceptance or rejection through exit codes.
See [implementation dependencies](README.md) for crate responsibilities.
Add `--offline` to Cargo commands if dependencies have already been downloaded.
