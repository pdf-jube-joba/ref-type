# Elaboration

`Checker` converts `resolve::Project` into kernel terms in a shared `Expression` arena and invokes type checking and declaration registration.

| Location | Responsibility |
| --- | --- |
| [api.rs](src/api.rs) | HIR checking, diagnostics, goals, statistics, and checkpoints |
| [elaborator](src/elaborator) | Implicit arguments and instantiation of blocks, induction, records, and modules |
| [analysis.rs](src/elaborator/analysis.rs) | Display types, name references, and query output |
| [metavariables.rs](src/metavariables.rs) | Hole origins and solver calls |
| [raw](src/raw) | Source views, module environments, and declaration IDs |
| [lowering](src/lowering) | Parameter capture, context arguments, and kernel registration |
| [kernel_bridge.rs](src/kernel_bridge.rs) | Connecting deferred instantiation to the kernel API |

Type checking, unification, reduction, reflection, and binding operations are delegated to the kernel; `finish` checks all metavariables and pending constraints when a declaration is finalized.
Module parameters retain named IDs; parameters referenced by kernel inputs are captured in dependency order.
Parameters unconstrained by dependencies are ordered by package and source location, independently of artifact restoration order.

Instantiation is indexed by the original module and argument list, sharing unchanged declarations and argument lists known to be equivalent.
Creating an instantiation avoids scanning all previous argument lists; necessary convertibility checks are delegated to the kernel.
Comparison caches are bounded; conversion failures during lookup are retried as the environment advances.
Namespaces are views with immutable original member indices and shared arguments; only looked-up members are instantiated.
Sparse tables reserve declaration IDs without allocating declaration cells for unreferenced members.
View identity includes the original generation, arguments, local context, and Program context, separating nominal identity from body instantiation.
Argument lists use shared arrays; bodies are generated lazily.
Original module argument lists are also shared, and their indices are rebuilt when parameters are added or artifacts merged.
Logical definitions without local contexts register their original body with the kernel once; specialized references call it with explicit module arguments.
Named imports, imports with local variables, and Program instantiations retain mappings between their declarations and checking contexts in views.
Referenced bodies and argument dependencies are instantiated before borrowing the kernel environment.
Substitution-map composition is shared as a DAG; each map/key pair is examined once during lookup, including failed lookups.
Finalizing an instantiation compacts only local tables, preserving shared parent substitution tables.

## API and diagnostics

`Checker::check` checks in a fresh checking environment.
`analysis`, `statistics`, and `kernel_environment` return inspection data, statistics, and the verified environment.
Diagnostics carry contexts, judgments, constraints, and source locations; [diagnostics.rs](src/diagnostics.rs) bounds their displayed size.

## Environment checkpoints

`check_range` processes an interval of the checking order; `check_range_with_progress` also reports each step's position and duration.
`restore_environment` reconnects raw and kernel arenas from a compressed checkpoint.
[declaration_checkpoint.rs](src/raw/declaration_checkpoint.rs) stores argument lists and substitutions in shared tables and streams encoded declaration rows.
[module_checkpoint.rs](src/raw/module_checkpoint.rs) restores sharing of immutable namespace name tables and labels.
`PackageChecker::checkpoint` retains the resolver, checking environment, and completed steps; `restore` reconnects current sources and name references.
Native session persistence stores expression pages and chunked indices as immutable objects, loading bodies from the pages needed.
[sema](../sema/README.md#reuse) handles matching and persistence.

## Package artifacts

`PackageChecker::artifact_boundary` records an ownership boundary; `export_artifact_for_input` separates the resolver and checking environment into distinct objects.
`ArtifactCatalog` maps input keys and persistent identities to runtime IDs.
Identity kinds and owning artifacts are collected in shared tables; individual mappings use integer indices.
Raw/kernel data forms a shared DAG; dependency expressions, macros, and substitution maps reference their owning artifacts.
Immutable snapshots of dependency maps preserve existing references even when maps grow during partial-artifact merging.
Namespace substitutions receive content identities; generated internal modules are identified per persisted artifact.
Frontend atom metadata is selected by reachability from persisted expressions, regardless of when it was generated.
Imports containing local variables share specialized declarations and namespaces, keyed by caller and logical/Program checking contexts.

`import_artifact` publishes the environment and catalog after ID reservation, relocation, and validation.
`import_artifact_owned` consumes the checker and catalog and discards both on failure.
`append_selected_with_checkpoints` processes unchecked steps in selected modules and their parents.
`export_resume` / `import_resume` preserve and restore the checking position; `import_resume_owned` is the consuming variant.
`append_selected_with_artifact_checkpoints` saves package deltas directly from a borrowed environment.
Before saving large environments, recomputable checking caches are released to make room for encoding buffers.
