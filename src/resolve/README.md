# Name resolution and HIR

`resolve::resolve` resolves AST names to binding IDs and returns a `Project` before type inference.

| Representation | Contents |
| --- | --- |
| `hir::ModuleId` | Modules and syntactic namespace instances |
| `hir::BindingId` | Declaration, parameter, and local-variable bindings |
| `hir::Name` / `LocalAccess` | Display names and binding targets / resolved references |
| `Project::bindings` / `imports` | Global binding ownership and parameter positions / imported namespaces |
| `Project::order` | Checking order for parameters and declarations |
| `Project::references` | Reference targets and source locations |

IDs are valid within one `Project` and are mapped to checking-environment IDs during elaboration.
`CheckStep::Parameters` and `Declaration` represent the checking order, placing reference targets before their uses.
Structural traversal uses `visit`; failures use `Diagnostic` with a module path and source location.

## Expansion

Macro names are collected throughout a module body; a child binding shadows a parent binding with the same name.
Macro references resolve in the completed definition-site scope, ordinary term names in the definition-site term environment, and captures at the call site.
Binding IDs preserve hygiene; expanded declarations and queries retain definition-site reference information.

Module arguments also undergo name resolution; type checking and typed instantiation are delegated to elaboration.
Only selected namespace paths are constructed, and children inherit the parent's argument environment.
Structure-value field references and preparatory imports are updated to use the same module ID.
Program parameter reflection retains the original ID and argument expression in `Reflect`.
`x.field` remains a projection carrying the field name.

## Package artifacts

`Session::boundary` records an ownership boundary; `export_package` saves subsequently added scopes, bindings, declarations, macros, and structure information.
A package stores each distinct local macro template once. Aliases of an existing dependency template refer to its binding slot in the relocated dependency scope. Specializations with the same definition ID can carry different captured bindings.
`reserve_import` reserves IDs; `import_package` relocates and validates references before publication.
`restore_sources` reconnects each shared template to the current snapshot once and reconnects the introduction location of every alias separately.

See [benchmarks](../../benchmarks/README.md) for measurements, and [macros](../../docs/language/macro.md) and [structures](../../docs/language/structure.md) for expansion rules.

Substitution and instantiation of structure namespace arguments process children of the original syntax tree before specializing the reference target.
Revisiting namespace arguments inserted by specialization in the same traversal would repeatedly expand the same references inside those arguments and never terminate.
`walk_sexp_postorder` processes each original child once; ordinary macro traversal keeps its ordering in `walk_sexp_control`.
This order also ensures finite instantiation when a fiber direct sum is passed to nested structure arguments, as in tangent-bundle addition.
