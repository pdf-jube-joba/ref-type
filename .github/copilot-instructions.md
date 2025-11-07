This repository implements a small proof-checker language split into a "front" (parser/elaboration) and a "kernel" (calculus, type checking, derivations).

Keep these quick facts in mind when editing or adding features:

- Architecture (big picture):
  - `src/front/` implements the surface language: parsing, syntax, resolver/elaboration. Key files: `src/front/src/parse.rs`, `src/front/src/syntax.rs`, `src/front/src/resolver.rs`, `src/front/src/printing.rs`.
  - `src/kernel/` is the theory core: expressions, calculus, derivation building and type-checking. Key files: `src/kernel/src/calculus.rs`, `src/kernel/src/derivation.rs`, `src/kernel/src/inductive.rs`, `src/kernel/src/exp.rs`, `src/kernel/src/printing.rs`.
  - `src/cli/` provides a small CLI and a dev web server. See `src/cli/src/main.rs` for how the CLI ties `front` and `kernel` together (it calls `front::parse::str_parse_modules`, `front::resolver::GlobalEnvironment`, then uses `kernel::printing::map_derivation`).

- How changes flow
  - New surface syntax -> update `front::syntax` + parser in `front::parse`.
  - Elaboration / name resolution -> update `front::resolver` to emit kernel-compatible modules.
  - Kernel extensions (calculi, type rules, printers) -> update `kernel` modules and the derivation builder.

- Build / test / run commands (examples)
  - Build entire workspace: `cargo build --workspace` (or `cargo build` at repo root).
  - Run tests: `cargo test --workspace` (or `cargo test -p front`, `-p kernel` to target one crate).
  - Run CLI file mode: `cargo run -p cli -- File path/to/example.rt` (see `src/cli/src/main.rs` for command names).
  - Run the dev web server: `cargo run -p cli -- Serve --port 8080` then open `http://127.0.0.1:8080`.
  - The project also contains many example proof files under `tests/` and `tests/ok` — use those as integration inputs.

- Project conventions and patterns
  - Clear separation: "front" is purely parsing/elaboration; it should not contain kernel typechecking logic. Keep kernel-facing data structures stable and convert to them in `front::resolver`.
  - Printing / diagnostic path: `kernel::printing` contains helpers that the CLI maps into JSON-friendly structures (see `src/cli/src/main.rs` where `kernel::printing::map_derivation` is used).
  - Tests: unit tests live inside each crate (`*_src/tests.rs`) and there is an examples folder (`tests/ok`, `tests/ng`). New examples belong in `tests/` not in source files.
  - Documentation is primarily in Japanese; follow existing comment and docstring style.

- Integration points to watch
  - `front::resolver::GlobalEnvironment` is the main entrypoint for composing modules and collecting logs/derivations.
  - `kernel::derivation` and `kernel::builder` form the internal derivation representation—changes here affect how proof trees are printed/stored.

- Small, practical heuristics for PRs
  - Add a small unit test in the relevant crate that demonstrates the change (front: add a parsing test; kernel: add a derivation or typing test). See `src/front/src/tests.rs` and `src/kernel/src/tests.rs` for examples.
  - Prefer adding examples under `tests/` for CLI-level behavior. Use `cargo run -p cli -- File tests/ok/<example>.txt` to reproduce.
  - When modifying public kernel types, update `kernel::printing` to preserve readable error/derivation output used by the CLI/UI.

If anything in this summary is unclear or you want more examples (small parsers, a sample elaboration change, or a guided PR checklist), tell me which area and I will expand the instructions. 
