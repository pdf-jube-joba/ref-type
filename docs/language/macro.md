# Macros

Visible macros from the current module and its parents can be used directly; introduce macros from other modules with `\use`.
Definitions and use declarations apply throughout the module body and its child modules. A child binding shadows a parent binding with the same name.
Duplicate introduced names within a module are errors, whether introduced by definitions or use declarations.

```text
\math-macro add($left, \+, $right) := operation $left $right;
\macro tagged($term, "keep") := $term;
\use ImportAlias.macroName;
\use ImportAlias.Child[A := A].macroName \as child_macro;
\use \root.Templates[A := A, refl := leftRefl].reflexive \as refl_left;
\use \root.Templates[A := A, refl := rightRefl].reflexive \as refl_right;

\(x + y \)
tagged!{value "keep"}
```

`\use` supports selection through import aliases and direct module instantiation.
Instances of the same definition with different arguments can coexist under different introduced names.

```text
\module Example(A: \Set, a, b: A) {
  \definition before: a = a := \refl(value!{});
  \macro value() := a;
  \module Child {
    \definition law: b = b := \refl(value!{});
    \macro value() := b;
  }
}
```

## Patterns and calls

Separate pattern elements with commas in definitions; separate call elements with whitespace or token boundaries.
The macro name and `!` must be adjacent.

| Pattern | Captures or matches |
| --- | --- |
| `$name` | One ordinary expression |
| `name` | One symbol or quoted token, in named macros |
| `..name` | The remaining sequence, in named macros; at most one at the end of each sequence |
| `\+` | A fixed symbol token |
| `"tag"` | A fixed quoted token |
| `(pattern, ...)` | A nested sequence |

The reserved symbols `->`, `~>`, `<-`, `=>`, `:=`, `|`, `:`, `;`, `.`, `,`, `=`, `!`, `::`, and `^` cannot be fixed macro tokens.
Math macro captures must use `$name`, and each math macro pattern must contain at least one fixed symbol or quoted token.
Capture names must be unique across the entire pattern, including nested sequences.
Use `{ f x }` to pass an ordinary compound expression as one argument, and `( ... )` for a nested macro sequence.

Free names in a template resolve at the definition site; captured expressions resolve in the call-site scope.
Binders introduced by a macro do not capture names from the call site.
For a capture containing `_`, the values inferred at each expanded occurrence are equated with one contextual metavariable.
If the capture itself contains a lambda, the entire expression is compared under its binders.
Separate captures and separate calls are inferred independently.
Math macros match the entire sequence at each parenthesis level. When several candidates match, selection prefers the leftmost fixed token, then the shortest distance from the call-site scope, then the introduction order within each module.

## Token matching and recursion

Named macro templates can use `\tmatch`.

```text
\macro last(..r) := \tmatch r {
  | () => defaultValue
  | ($t) => $t
  | ($t, ..rest) => last!{..rest}
};
```

Here `defaultValue` is an expression already in scope.
Branches are tried in order; only the first matching branch is expanded.
Patterns can match fixed symbols, quoted tokens, and sequences; `_` matches any input.
Exhaustiveness is not required, but an actual call with no matching branch is an error.
Branch captures are scoped to that branch. Free names in every branch are validated when the macro is declared.

> [!warning]
> Parenthesized sequences are not flattened automatically.

Macros referenced in a template bind to the completed definition-site scope, supporting forward references and mutual recursion.
Introducing a macro under an alias preserves the original instantiation for internal references and self-references.
Ordinary term names resolve in the term environment at the definition site; module arguments in a use declaration resolve in the term environment at that declaration.
Module headers and parameter types use the parent's macro scope.
Cyclic instantiation dependencies report the dependency path and declaration locations.
The expansion depth limit is 128.
