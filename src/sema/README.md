# Semantic API and caching

The CLI and LSP check immutable [SourceSnapshot](../project/README.md#source-snapshot) values through `sema::Database`.
See [Usage](../USAGE.md) for CLI commands.

## API

```rust
use sema::{Database, ParseKind, SourceSnapshot};
let source = SourceSnapshot::read("libs/std")?;
let mut db = Database::with_cache(source.default_cache_directory());
let checked = db.check(&source);
assert!(checked.is_success());
let path = "libs/std/src/Data/Nat.ref";
let edited = source.with_file(path, std::fs::read_to_string(path)?);
let parsed = db.parse(&edited, path, ParseKind::Module);
```

| Query | Result |
| --- | --- |
| `parse` / `parse_project` | File / package syntax and diagnostics |
| `module` / `file` / `check` | Semantic results for the specified scope |
| `Database::declaration` | Semantic result containing a declaration |
| `SemanticResult::declaration` | Declaration for a `DeclarationId` |
| `definition_at` / `references_to` / `type_at` | Definitions, references, and display types |
| `all_diagnostics` / `goals` / `outputs` | Diagnostics, goals, and query output |

Locations consist of an absolute path and a half-open range of UTF-8 byte offsets.
Declaration IDs use a module path and name; type-associated items use `Type::member`.
`Verified` indicates completed verification; `Incomplete` indicates partial results.

## Reuse

`read_snapshot` checks current contents, including dependencies.
The source cache is bounded at 64 MiB and 16,384 entries; parse, module, and query caches retain the current and previous read generations.
Unchanged queries reuse the same `Arc`, including failed results.
`memory_cache_stats` reports retained sizes; `clear_memory` releases database-owned data.
Caller-owned `Arc` values and live arenas are managed separately.

Package input keys include the implementation, configuration, identities, sources, manifests, and named direct dependencies; artifact keys additionally include the checking scope.
Keys are independent of dependency visitation order and consumer paths, allowing different consumers to reuse verification of the same package.
`force_local` rechecks the entry package or workspace members and uses content-matching results for external dependencies.
Unsaved LSP edits use the same matching rules.

Manifests in `artifacts/` reference per-module verification results in `objects/`.
Queries that need only results are answered without expanding the type-checking environment.
Checking sessions own the resolver, raw/kernel data, and completion ledger retained by the `Database`.
Source module IDs and child indices are reserved first; requested bodies undergo name resolution on demand.
Name-resolution argument environments use a shared DAG of deltas and substitutions, expanding values needed by actual references.
Name and import tables passed to checking are also shared; additional requests append changed packages' syntax trees and new declarations.
After checking, kernel types and bodies and templates needed for future structure/macro expansion are retained, while checking inputs for completed steps are released.
Declarations in the dependency closure are queued; completed steps are skipped in later package requests or checking-scope extensions.
Reference locations and per-module analysis are shared; caller-retained results remain tied to their past snapshots.
Inputs, implementation, configuration, and forced-checking scopes are matched to decide whether previous sessions and saved artifacts can be reused.
A `--full-check` worker starts a new verification generation with empty storage and shares declarations completed within that run.

Saved sessions record package inputs, resolved source scopes, checked scopes, and append order.
Checkpoints connect resolver and raw indices, completed steps, and expression-graph page references.
Resolver name tables, argument environments, reference paths, and namespace mappings are saved as shared DAGs and preserve sharing after restoration.
Session metadata also uses content-defined chunks of 16–128 KiB, reusing objects with identical contents.
Restoration reads saved objects sequentially without a buffer for the entire expanded serialization.
Kernel bodies load only the pages needed; persistence also reuses objects for finalized pages.
Later checking continues with the same internal IDs without expanding all dependency bodies at once.
Package-completion indices are saved when the step count has doubled since the previous save, at external-dependency completion boundaries, and when the entire request completes.
Each encoding covers the whole current session, but this schedule limits the cumulative cost of repeatedly saving a growing prefix for every package.

Objects contain postcard data plus kind, codec, length, and checksum; native builds use zstd, while WebAssembly uses deflate.
Prefix checking steps and inputs are matched, and corrupted environments are rebuilt.
Verification results can still be saved when the environment cannot be persisted.

`checkpoints/` retains prefixes of checks in progress.
Even while checking dependencies, checkpoints are published under the active request's key, preserving its completion ledger during recovery.
Keys are derived from the input and entire requested scope, independently of individual package cache hits or visitation order.
Saving a completed environment also updates the same resume entry, preventing selection of an older interrupted checkpoint.
`checkpoint_interval` sets the save interval at module completion; the default is 30 seconds, and zero considers every boundary.
Save-cost-based waiting is capped by the configured interval, which remains unchanged after successful saves.
Checkpoints are collected after verification results are published.
Under sustained memory pressure, cache collection runs immediately, while checkpoint saving waits for a module boundary after this interval.
Resumption also checks forced-verification settings and treats partially checked states as checkpoints.

Publication, pinning, and GC use store locks and leases, protecting artifacts in use and their dependency closures.
The supervisor shares a lease across workers; OS locks identify leases belonging to exited processes.
Storage is unlimited by default; `set_cache_budget` can impose a limit when needed.
Old unused manifests and checkpoints and unreferenced objects are collected.

`cache_store_stats` reports I/O, reuse, resumption, save failures, compression/decompression, and collection sizes.
While `retained_bytes_is_upper_bound` is set, retained size is a conservative cumulative value; GC updates it to the actual size.
Supervisor source snapshots and temporary communication files are excluded from storage accounting.
The implementation fingerprint tracks relevant sources, build scripts, dependency resolution, toolchain, target, features, and cfg, excluding test-only code.

`progress` reports per-module timings at completion; `progress_events` reports dependency graphs, phases, declaration/module completion, checkpoint saves and failures, and storage statistics.
`QueryStats::session` reports instantiation counts, namespace/substitution-table/declaration-cell counts, and expression-store retention.
Generated scopes are grouped under their original source modules; reused modules also count as complete.
See [artifact_store.rs](src/artifact_store.rs), [memory.rs](src/memory.rs), and [build.rs](build.rs) for implementation, and [tests](tests) for validation.
