# PTS kernel

Sorts, types, terms, and proofs share the `Expression` and `Node` representations in `kernel::syntax`.
An `Expression` is an interned handle in an `Arena`; child terms and binder types use the same arena.

| Module | Responsibility |
| --- | --- |
| [check](src/check.rs) | Typing judgments |
| [sort](src/sort.rs) | Sort axioms and product relations |
| [calculus](src/calculus.rs) | Binding, shifting, and substitution |
| [reduction](src/reduction.rs) | Reduction, evaluation, and conversion |
| [reflection](src/reflection.rs) | Program reflection |
| [metavariables](src/metavariables.rs) | Unification and pending constraints |
| [environment](src/environment.rs) | Declaration registration and the verified environment |
| [exports](src/exports.rs) | Relocation of package-owned declarations and shared expressions |
| [node_store](src/node_store.rs) | Stable expression handles and resident page management |
| [graph_store](src/graph_store.rs) | Connecting sessions to the immutable object store |

`Context` is a telescope of `Binding { var, ty }` entries ordered from outermost to innermost; each type is interpreted in the preceding context.
`Bound(0)` denotes the innermost variable; `SymbolId` is a display name, and alpha equivalence does not depend on names.

## Type inference and registration

```rust
use kernel::{check::Checker, environment::{Definition, Environment},
    ids::SymbolId, metavariables::MetaContext,
    sort::{BaseSort, Sort}, syntax::{Mode, Node}};

let mut env = Environment::new();
let arena = env.arena().clone();
let set = arena.sort(Sort::Base(BaseSort::Set(0)));
let identity = arena.alloc(Node::Lambda {
    mode: Mode::Pure,
    var: SymbolId::ANONYMOUS,
    domain: set,
    body: arena.bound(0),
});
let mut metas = MetaContext::new();
let ty = Checker::new(&env, &mut metas, vec![]).infer(identity)?;
let id = env.register_definition(&mut metas, Definition {
    context: vec![], ty, body: identity,
})?;
let reference = env.reference(id, vec![])?;
assert_eq!(Checker::new(&env, &mut metas, vec![]).infer(reference)?, ty);
# Ok::<(), Box<dyn std::error::Error>>(())
```

Public `infer` / `check` validate context formation and return `Error::Unresolved` if metavariables remain unsolved.
`register_definition` returns a `DefinitionId` after `finish` and strict type checking.
Definition references simultaneously substitute context arguments into the declared type and body; Program definitions also check their reflected counterparts before registration.
Elaboration retains module names and source locations.

`register_inductive` checks arity, constructor result types, sorts, and strict positivity.
`register_datatype` checks Program fields and parameters and registers their Set mirrors.
`IndElim` stores the motive telescope and body separately and checks each branch by substituting indices, the element, and recursive hypotheses.
See [check.rs](src/check.rs) for elimination restrictions and singleton elimination.

`IdElim` represents proposition-valued equality elimination and set-valued transport, checking the result according to the sort of `family`.
Set-valued transport preserves a neutral head; `TransportEq` proves the propositional equality between self-transport and the original value.
Equality certificates participate in type checking and ordinary structural traversal but are erased from conversion and unification comparisons.

## Refinements and metavariables

`SubsetIntro` checks an element and its membership evidence and returns the refinement type `TypeLift`.
Membership evidence is retained when weakening to the ambient set.
`Environment::erased_head` looks through introductions when observing values, giving conversion, application, membership, and elimination a common view of the value.

Metavariables have a declaration context and an expected type; arguments at each occurrence represent a substitution from that context.

| Operation | Role |
| --- | --- |
| `fresh` / `restrict` | Create a hole / restrict its context to a shared prefix |
| `infer` / `check` / `unify` | Generate constraints and unify |
| `solve_pending` / `finish` | Retry pending judgments / confirm completion of all checking obligations |
| `zonk` | Substitute solved metavariables |
| `snapshot` / `rollback` | Save and restore state around a trial |

The occurs check also detects cycles through candidates, expected types, and declaration contexts.
`finish` checks holes that are not reachable from the result as well.
Elaboration manages the surface distinction between `_` and `?`, along with their locations.

## Sharing and inspection

`Environment::boundary` and `export_since` collect declarations added by a package into an `EnvironmentExport`.
Dependency declarations are shared as references; reachable expressions are saved in child-first order.
`reserve_definitions` and `reserve_nominals` reserve IDs; `Arena::import_graph` restores the `ExpressionGraph` shared with the raw layer before declarations are relocated.
`Environment::import_export` validates references and reflection tables and shares overlapping partial artifacts after checking that declarations and expressions agree.
Unsolved metavariables are detected during export; `Meta` identities, also used for raw declaration references, are relocated through frontend mappings and `reserve_metas`.
On failure, added expressions and ID mappings are rolled back, preserving existing declaration tables.

Expressions occupy pages of 2,048 slots; reference and interning indices are independent of body residency.
The interning index stores 32-bit candidate keys and 32-bit expression references; collisions compare entire nodes to confirm identity.
The `Rc<Node>` returned by `Arena::read` pins the snapshot read at that time and remains usable after its page is spilled.
Temporary-expression cleanup during declaration registration also retains expressions reachable from published snapshots; discarded handles are not reused by ordinary allocation.
The native resident page budget defaults to 128 MiB and can be changed through `Arena::set_resident_budget` or `REF_TYPE_GRAPH_RESIDENT_MIB`.
`Arena::store_stats` returns retained sizes, read/write volumes, and spill counts.

Session persistence appends finalized pages to the `GraphStore` supplied by `with_graph_store`, reusing references to existing pages.
Checkpoints retain page references, live bitmaps, expression properties, and interning indices; bodies are read on demand.
Temporary spilling uses session-specific files with read/write buffers limited to 64 KiB.
The CLI places spill files on the cache filesystem and releases temporary copies once all checkpoint pages have been saved as immutable objects.
`REF_TYPE_GRAPH_SPILL_DIR` selects the spill directory; outside the CLI, the OS temporary directory is the default.
WebAssembly keeps data in memory without file spilling.

Structural traversal with binders is centralized in `Arena::map_children`.
The environment shares inference, weak-head reduction, conversion, contexts, type shifting, and simultaneous substitution; `cache_counts` reports entry counts.
When sharing tables reach their limits, they retain at most three quarters of entries, preferring reused entries.
Temporary nodes and sharing tables created during definition registration are collected while preserving live declarations, metavariables, diagnostics, and read snapshots.
Sharing tables are not serialized and are recomputed after restoration.
`reduction::first_difference` returns differing subterms after reduction and their paths.
See [Usage](../USAGE.md#diagnostics-and-profiling) for measurement instructions.
