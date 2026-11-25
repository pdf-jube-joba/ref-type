# Implementation dependencies

All implementation crates and the resolver benchmark share the root Cargo workspace and `Cargo.lock`.
Internal paths and shared external dependency versions are defined in the root `[workspace.dependencies]` table.
Crates enable additional features locally, including Serde reference-counted values, Postcard standard-library support, and Syn visitors.

| Crate | Responsibility | Direct internal runtime dependencies |
| --- | --- | --- |
| `timing` | Profiling and cost accounting | None |
| `diagnostics` | Shared diagnostic data | None |
| `artifact-derive` | Relocation derive macro | None |
| `artifact` | Artifact relocation and canonical data | `artifact-derive` |
| `syntax` | Parsing and surface syntax | `artifact`, `diagnostics` |
| `project` | Source snapshots, modules, packages, and workspaces | `syntax`, `diagnostics`, `timing` |
| `resolve` | Binding resolution, expansion, and HIR | `syntax`, `artifact`, `diagnostics`, `timing` |
| `kernel` | Core terms and verification | `artifact`, `diagnostics`, `timing` |
| `elaboration` | Inference and translation to kernel terms | `resolve`, `syntax`, `kernel`, `artifact`, `diagnostics`, `timing` |
| `sema` | Semantic queries, incremental checking, and persistent storage | `project`, `resolve`, `syntax`, `elaboration`, `diagnostics`, `timing` |
| `cli` | Command-line input, reporting, and process supervision | `sema` |

`resolve` uses `project` only for integration tests.
`artifact-derive` is a procedural macro dependency; it does not add a runtime service.
`sema/build.rs` fingerprints implementation sources and build inputs with `sha2`, `syn`, and `quote` for cache identity.
`cli` uses Rust's standard allocator and a Linux-only `libc` dependency for worker supervision.
Expression pages use the cache object store supplied by `sema`; in-memory checking does not create a separate paging store.
Native checkpoint compression uses Zstandard; WebAssembly uses `miniz_oxide`.

## Development commands

```sh
cargo build -p cli --locked
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
cargo fmt --all -- --check
```

Default Cargo commands select the implementation crates.
`--workspace` also builds and checks `benchmarks/`; its binaries use the same `target/` directory.
No implementation crate depends on benchmark or Python tooling code.

See [CLI usage](USAGE.md), [source acceptance tests](../tests/README.md), and [benchmarks](../benchmarks/README.md) for the separate entry points.
