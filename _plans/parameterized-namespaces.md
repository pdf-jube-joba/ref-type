# Substitution-based parameterized namespaces

The surface module/import syntax is unchanged. Modules are front-end sections:
imports bind namespaces and substitute their parameters, not applications in the
kernel's product calculus. There is no module-instance identity.

## Invariants

- Validate named module arguments in dependency order, before publishing an alias.
- Compose substitutions simultaneously and capture-avoidantly. Rename references
  in the source graph before substitution; never rename inserted caller arguments.
- Retain original-declaration provenance and the complete enclosing argument
  telescope (including phantom and proof arguments). After an outer substitution,
  resolve that provenance again. Convertible arguments of the same source reuse
  declaration IDs; distinct source inductives remain nominally distinct.
- Keep the identity decision in the front. Kernel conversion needs neither
  namespace arguments nor a declaration-application reduction rule.
- DefId remains front name/diagnostic metadata and a checked-declaration registry
  key. Kernel expressions use interned Annotated { body, classifier } nodes,
  never DefId references. The classifier preserves declared weakening; inference
  independently checks the body. Conversion transparently compares bodies.
- All structural substitutions and closure checks visit annotation classifiers as
  well as bodies, including Program reflection and embedded proof terms.
- Alias scopes and macro hygiene are front-only. Original declarations are checked
  even if unused; specialized declarations are materialized lazily and checked.
- Program associated-item type arguments remain explicit front substitutions.
  No namespace parameter is lambda-lifted; product rules are unchanged.

## Regression coverage

Repeated/convertible imports, nested aliases, inherited parent substitutions,
distinct sources and phantom arguments, proof parameters with Set-valued members,
Program records and associated definitions, macros, annotation weakening,
forged annotations, closure, and capture-avoiding body/classifier substitution.
