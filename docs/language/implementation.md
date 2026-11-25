# Implementation

The CLI checks source snapshots through `sema::Database`, which also exposes semantic queries for editor integration.

| Crate | Responsibility |
| --- | --- |
| [project](../../src/project/README.md) | Source snapshots, packages, workspaces, and external module loading |
| [syntax](../../src/syntax/README.md) | Lexing, parsing, AST, and source spans |
| [resolve](../../src/resolve/README.md) | Name resolution, macro and structure expansion, and HIR before type inference |
| [elaboration](../../src/elaboration/README.md) | Implicit arguments, surface syntax elaboration, module instantiation, and diagnostics |
| [kernel](../../src/kernel/README.md) | Type checking, unification, substitution, reduction, reflection, and declaration registration |
| [artifact](../../src/artifact/README.md) | Persistent package identities, canonical serialization, and relocation to runtime IDs |
| [sema](../../src/sema/README.md) | Semantic queries, dependencies, and caching of results and environments |

Sorts, types, terms, and proofs reside in an `Expression` arena shared by the kernel and elaboration.
Definitions retain their context, type, and body; references use a `DefinitionId` and context arguments.
When a declaration is finalized, `finish` checks for unresolved metavariables and pending constraints.

Checking sessions share resolver and raw/kernel environments and a completion ledger, allowing later package requests to reuse completed checking steps.
Native persistence connects inputs, checked scopes, resolver and raw indices, and expression-graph page references through checkpoints.
Restoration preserves internal IDs and loads the expression pages needed to continue checking.
Reuse requires matching the implementation, configuration, sources, dependency inputs, and scopes that require forced checking.

See [sema](../../src/sema/README.md#reuse) for storage formats and reuse.
See [CLI usage](../../src/USAGE.md) for execution, diagnostics, and profiling.
