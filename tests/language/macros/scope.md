# macros / scope

## macro name collision

同じ scope で macro 名が重複しているため、拒否される。

```toml case
id = "reject-macros.macro_name_collision"
scope = "module"
expect = "reject"
name = "MacroNameCollision"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro same() := value;
\macro same($other) := $other;
```

## token match branch scope

token match の別の分岐で束縛された capture を参照しているため、拒否される。

```toml case
id = "reject-macros.token_match_branch_scope"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := \tmatch r { | ($x) => $x | () => $x };
```

## use requires import

macro の使用元となる module が import されていないため、拒否される。

```toml case
id = "reject-macros.use_requires_import"
scope = "module"
expect = "reject"
name = "UseRequiresImport"
```

```ref
\use missing.some_macro;
```

## definition scope hygiene

macro 展開が定義位置の名前と使用位置の binder を区別するため、受理される。

```toml case
id = "accept-macros.definition_scope_hygiene"
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

## forward math template

後で定義された math template も module 本体から利用できるため、受理される。

```toml case
id = "accept-macros.forward_math_template"
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

## import forward scope

macro の import が module 本体全体に有効であるため、受理される。

```toml case
id = "accept-macros.import_forward_scope"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates { \macro reflexive($x) := \refl($x); }
\module Repro(A: \Set, a: A) {
  \import \root.Templates[] \as Templates;
  \module Child { \definition law: a = a := reflexive!{a}; }
  \use Templates.reflexive;
}
```

## import inherited

子 module が親の macro import を引き継ぐため、受理される。

```toml case
id = "accept-macros.import_inherited"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates { \macro reflexive($x) := \refl($x); }
\module Repro(A: \Set, a: A) {
  \import \root.Templates[] \as Templates;
  \use Templates.reflexive;
  \module Child {
    \definition law: a = a := reflexive!{a};
  }
}
```

## import repeated in child

子 module で同じ macro を再度 import できるため、受理される。

```toml case
id = "accept-macros.import_repeated_in_child"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Templates { \macro reflexive($x) := \refl($x); }
\module Repro(A: \Set, a: A) {
  \import \root.Templates[] \as Templates;
  \use Templates.reflexive;
  \module Child {
    \use Templates.reflexive;
    \definition law: a = a := reflexive!{a};
  }
}
```

## module visibility

import した module の macro を宣言された scope から利用できるため、受理される。

```toml case
id = "accept-macros.module_visibility"
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

## named forward reference

名前付き macro を宣言位置より前で使えるため、受理される。

```toml case
id = "accept-macros.named_forward_reference"
scope = "module"
expect = "accept"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro early() := later!{}; \macro later() := value;
```

## recursive hygiene

再帰的な macro 展開でも binder の capture を避けるため、受理される。

```toml case
id = "accept-macros.recursive_hygiene"
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

