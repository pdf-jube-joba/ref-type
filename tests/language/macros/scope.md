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


## import した macro の入れ子

Wrapper の macro を別 module で使っても、定義元が import した macro とその引数を参照できる。

```toml case
id = "instantiated_macro_keeps_macros_used_by_its_definition_module"
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

## 使用位置の同名変数

使用位置に別の型の provided があっても、macro は定義位置で渡された provided を参照する。

```toml case
id = "imported_macro_resolves_free_names_at_its_definition_site"
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

## lexical shadowing and definition site internal references

子の macro は同名の親の macro を隠すが、親で定義した template 内の参照は親の macro を指す。

```toml case
id = "lexical_shadowing_and_definition_site_internal_references"
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
    \module Grandchild { \definition local: b = b := \refl(value!{}); }
  }
  \module Sibling { \definition local: a = a := \refl(value!{}); }
}
```

## forward mutual recursion and aliased self recursion

互いに呼ぶ macro でも入力 sequence が短くなるため停止し、alias を経て呼び出せる。

```toml case
id = "forward_mutual_recursion_and_aliased_self_recursion"
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

## direct use flattens structure arguments

structure の値を module の引数に渡し、直接 use した macro からその field を利用できる。

```toml case
id = "direct_use_flattens_structure_arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Playground { \structure Point[Carrier: \Set] { value: Carrier }
  \module T(A: \Set, point: Point[A]) { \macro value() := point.value; }
  \module M(A: \Set, a: A) {
    \definition law: a = a := \refl(value!{});
    \use \root.Playground[].T[A := A, point := Point[A] { value := a }].value;
}}
```

## math in use arguments can use independent local templates

use の引数の math template は独立した局所定義から展開できる。

```toml case
id = "math_in_use_arguments_can_use_independent_local_templates"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module T(A: \Set, a: A) { \macro value() := a; }
\module M(A: \Set, a: A) {
  \definition law: a = a := \refl(value!{});
  \use \root.T[A := A, a := \(a + a\)].value;
  \math-macro plus($x, \+, $y) := $x;
}
```

## math use arguments report their own instantiation cycle

use しようとする math macro 自身が use の引数の計算に必要なので、循環する依存として拒否される。

```toml case
id = "math_use_arguments_report_their_own_instantiation_cycle"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module T(A: \Set, a: A) { \math-macro plus($x, \+, $y) := a; }
\module M(A: \Set, a: A) { \use \root.T[A := A, a := \(a + a\)].plus; }
```
