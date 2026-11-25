# Macro scope and hygiene

## Macro name collision

Macro names are duplicated in the same scope.

```toml case
id = "macro-name-collision"
scope = "module"
expect = "reject"
name = "MacroNameCollision"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro same() := value;
\macro same($other) := $other;
```

## Token match branch scope

A capture bound in a different token-match branch is referenced.

```toml case
id = "token-match-branch-scope"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := \tmatch r { | ($x) => $x | () => $x };
```

## Macro use requires a known namespace

The use declaration references a namespace that is not in scope. Direct module instantiation is supported, but this path names neither an import alias nor a known package.

```toml case
id = "macro-use-unknown-namespace"
scope = "module"
expect = "reject"
name = "UnknownMacroNamespace"
```

```ref
\use missing.some_macro;
```

## Definition scope hygiene

Macro expansion distinguishes definition-site names from use-site binders.

```toml case
id = "definition-scope-hygiene"
scope = "module"
expect = "accept"
name = "DefinitionScope"
parameters = '''A: \Set(0), x: A'''
```

```ref
\definition chosen: A := x;
\macro from_definition() := chosen;
\macro constant($body) := \fun (x: A) => $body;
\macro mixed() := (\fun (x: A) => x) x;

\definition chosen_at_call_site: A := from_definition!{};
\definition keeps_outer_x: A -> A -> A :=
    \fun (x: A) => constant!{x};
\definition keeps_free_x: A := mixed!{};
```

## Forward math template

Math templates defined later are also available in the module body.

```toml case
id = "forward-math-template"
scope = "module"
expect = "accept"
name = "LaterMacro"
parameters = '''A: \Set(0), x: A, y: A'''
```

```ref
\definition first: A -> A -> A :=
    \fun (left: A) => \fun (right: A) => left;
\macro select($left, $right) := \($left + $right \);
\math-macro plus($left, \+, $right) := first $left $right;

\definition result: A := select!{x y};
```

## Import forward scope

Macro imports are effective throughout the module body.

```toml case
id = "import-forward-scope"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates {
  \macro reflexive($x) := \refl($x);
}
\module ImportForwardScope(A: \Set, a: A) {
  \import \root.Templates[] \as Templates;
  \module Child {
    \definition law: a = a := reflexive!{a};
  }
  \use Templates.reflexive;
}
```

## Import inherited

Child modules inherit parent macro imports.

```toml case
id = "import-inherited"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates {
  \macro reflexive($x) := \refl($x);
}
\module ImportInherited(A: \Set, a: A) {
  \import \root.Templates[] \as Templates;
  \use Templates.reflexive;
  \module Child {
    \definition law: a = a := reflexive!{a};
  }
}
```

## Import repeated in child

A child module can import the same macro again.

```toml case
id = "import-repeated-in-child"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates {
  \macro reflexive($x) := \refl($x);
}
\module ImportRepeatedInChild(A: \Set, a: A) {
  \import \root.Templates[] \as Templates;
  \use Templates.reflexive;
  \module Child {
    \use Templates.reflexive;
    \definition law: a = a := reflexive!{a};
  }
}
```

## Module visibility

Imported module macros can be used from their declared scopes.

```toml case
id = "module-visibility"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module MacroProvider(A: \Set(0), value: A) {
    \definition stored: A := value;
    \macro supplied() := stored;
    \math-macro imported_plus($left, \+, $right) := stored;
}

\module MacroConsumer(A: \Set(0), value: A) {
    \import \root.MacroProvider[A := A, value := value] \as provider;
    \use provider.supplied;
    \use provider.imported_plus;

    \definition named_result: A := supplied!{};
    \definition math_result: A := \(value + value \);

    \macro parent_value() := value;
    \module Child {
        \definition inherited_result: A := parent_value!{};
    }
}
```

## Named forward reference

Named macros can be used before their declaration.

```toml case
id = "named-forward-reference"
scope = "module"
expect = "accept"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro early() := later!{};
\macro later() := value;
```

## Recursive hygiene

Recursive macro expansion also avoids variable capture by binders.

```toml case
id = "recursive-hygiene"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module RecursiveProvider(A: \Set(0), value: A) {
    \macro keep($chosen, ..r) := \tmatch r {
        | () => $chosen
        | ($ignored, ..tail) => (\fun (x: A) => keep!{$chosen ..tail}) value
    };
    \macro outer(..r) := (\fun (x: A) => keep!{x ..r}) value;
    \macro last(..r) := \tmatch r {
        | () => value
        | ($t) => $t
        | ($t, ..tail) => last!{..tail}
    };
    \macro save_first(tk, $saved, ..r) := \tmatch r {
        | ($value, ..tail) => (\fun (x: A) => \tmatch tk {
            | "save" => save_first!{"keep" x ..tail}
            | _ => save_first!{"keep" $saved ..tail}
        }) $value
        | () => $saved
    };
    \macro bind_again($chosen, ..r) := \tmatch r {
        | () => $chosen
        | ($t, ..tail) => (\fun (x: A) => bind_again!{{ (\fun (ignored: A) => $chosen) x } ..tail}) value
    };
}
\module RecursiveConsumer(A: \Set(0), a: A, b: A) {
    \import \root.RecursiveProvider[A := A, value := a] \as provider;
    \use provider.keep;
    \use provider.outer;
    \use provider.last;
    \use provider.bind_again;
    \use provider.save_first;
    \definition caller_scope: (\fun (x: A) => keep!{x a b}) b = b := \refl(b);
    \definition definition_scope: outer!{b b} = a := \refl(a);
    \definition empty: last!{} = a := \refl(a);
    \definition recursive: last!{a a b} = b := \refl(b);
    \definition saved_binder: save_first!{"save" a b a} = b := \refl(b);
    \definition recursive_binders: bind_again!{b a a} = b := \refl(b);
}
```


## Nested imported macros

Using Wrapper's macro in another module can still reference macros and arguments imported at the definition site.

```toml case
id = "instantiated-macro-keeps-macros-used-by-its-definition-module"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(A: \Set(0), value: A) {
  \macro base_value() := value;
}
\module Wrapper(A: \Set(0), value: A) {
  \import \root.Base[A := A, value := value] \as base;
  \use base.base_value;
  \macro wrapped() := base_value!{};
}
\module Consumer(A: \Set(0), value: A) {
  \import \root.Wrapper[A := A, value := value] \as wrapper;
  \use wrapper.wrapped;
  \definition result: A := wrapped!{};
}
```

## Same-named variables at the use site

Even if a different-typed provided exists at the use site, the macro references the provided passed at its definition site.

```toml case
id = "imported-macro-resolves-free-names-at-its-definition-site"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Provider(A: \Set(0), provided: A) {
  \macro supplied() := provided;
}
\module Consumer(A: \Set(0), B: \Set(0), a: A, provided: B) {
  \import \root.Provider[A := A, provided := a] \as provider;
  \use provider.supplied;
  \definition result: A := supplied!{};
}
```

## Lexical shadowing and definition site internal references

A child macro shadows a same-named parent macro, but references in templates defined in the parent still target the parent macro.

```toml case
id = "lexical-shadowing-and-definition-site-internal-references"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module M(A: \Set, a, b: A) {
  \definition before: a = a := \refl(value!{});
  \macro wrapped() := value!{};
  \macro value() := a;
  \module Child {
    \definition local: b = b := \refl(value!{});
    \definition captured: a = a := \refl(wrapped!{});
    \macro value() := b;
    \module Grandchild {
      \definition local: b = b := \refl(value!{});
    }
  }
  \module Sibling {
    \definition local: a = a := \refl(value!{});
  }
}
```

## Forward mutual recursion and aliased self recursion

Mutually calling macros terminate as the input sequence shrinks and can be invoked through aliases.

```toml case
id = "forward-mutual-recursion-and-aliased-self-recursion"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates(A: \Set, a: A) {
  \macro first(..xs) := \tmatch xs { | () => a | ("next", ..rest) => second!{..rest} };
  \macro second(..xs) := \tmatch xs { | () => a | ("next", ..rest) => first!{..rest} };
}
\module Consumer(A: \Set, a: A) {
  \definition law: a = a := \refl(start!{"next" "next" "next"});
  \use \root.Templates[A := A, a := a].first \as start;
}
```

## Direct use flattens structure arguments

A structure value can be passed as a module argument, making its fields available to a directly used macro.

```toml case
id = "direct-use-flattens-structure-arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module DirectUseFlattensStructureArguments {
  \structure Point[Carrier: \Set] := { value: Carrier };
  \module T(A: \Set, point: Point[A]) {
    \macro value() := point.value;
  }
  \module M(A: \Set, a: A) {
    \definition law: a = a := \refl(value!{});
    \use \root.DirectUseFlattensStructureArguments[].T[A := A, point := Point[A] { value := a }].value;
}}
```

## Math in use arguments can use independent local templates

A math template in a use argument can expand from an independent local definition.

```toml case
id = "math-in-use-arguments-can-use-independent-local-templates"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module T(A: \Set, a: A) {
  \macro value() := a;
}
\module M(A: \Set, a: A) {
  \definition law: a = a := \refl(value!{});
  \use \root.T[A := A, a := \(a + a\)].value;
  \math-macro plus($x, \+, $y) := $x;
}
```

## Math use arguments report their own instantiation cycle

The math macro being used is itself needed to compute its use arguments, so the cyclic dependency is rejected.

```toml case
id = "math-use-arguments-report-their-own-instantiation-cycle"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module T(A: \Set, a: A) {
  \math-macro plus($x, \+, $y) := a;
}
\module M(A: \Set, a: A) {
  \use \root.T[A := A, a := \(a + a\)].plus;
}
```
