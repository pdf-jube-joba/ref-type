# 型注釈による検査

## 論理の型注釈

期待型から lambda の引数を推論し、macro 展開と module の特殊化を経ても型注釈を保つ。

```toml case
id = "ascription_infers_types_and_works_through_macros_and_modules"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Annotated(A: \Set, a: A) {
  \macro typed($x) := $x \of A;
  \definition value: A := typed!{a};
  \definition inferred: A := a \of _;
  \definition identity: A -> A := (\fun (x: _) => x) \of A -> A;
  \definition applied: A := (identity \of A -> A) a;
  \definition kind: \SetKind := \Set \of \SetKind;
  \definition local: A := \block {
    \let x: A := a \of A \then
    \return x
  };
}
\module Use {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.Annotated[A := Unit, a := Unit::unit] \as M;
  \definition value: Unit := M.value;
  \definition equal: M.value = Unit::unit := \refl(Unit::unit);
}
```

## Program の型注釈

value と computation に各 judgement の型注釈を付け、関数適用と reflection で利用できる。

```toml case
id = "ascription_supports_program_values_computations_and_reflection"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module AnnotatedProgram(A: \VType, a: A) {
  \definition value: A := a \of A;
  \definition inferred: A := a \of _;
  \definition computation: \F A := (\return a) \of \F A;
  \definition identity: A -> A := (\fun (x: _) => \return x) \of A -> A;
  \definition applied: \F A := (identity \of A -> A) (a \of A);
  \definition explicit: \F A := (identity \of A ~> \F A) a;
  \definition thunk: \U(A ~> \F A) := \thunk identity;
  \definition forced: \F A := \force (thunk \of \U(A ~> \F A)) a;
  \definition reflected: value^ = a^ := \refl(a^);
  \check computation: \F A;
  \check a \of A: A;
}
\module ProgramUse {
  \inductive Bool: \VType := | yes: Bool;
  \import \root.AnnotatedProgram[A := Bool, a := Bool::yes] \as M;
  \definition value: Bool := M.value;
  \definition computation: \F Bool := M.forced;
}
```

## 論理の異なる型

元の項と型注釈の型が一致しないため拒否される。

```toml case
id = "wrong-ascription-0"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \Set, B: \Set, a: A'''
```

```ref
\definition value: A := a \of B;
```

## Program value の異なる型

元の項と型注釈の型が一致しないため拒否される。

```toml case
id = "wrong-ascription-1"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition value: A := a \of B;
```

## Program computation の異なる型

元の項と型注釈の型が一致しないため拒否される。

```toml case
id = "wrong-ascription-2"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition value: \F A := (\return a) \of \F B;
```

## subset から基底型への注釈

subset の要素を基底型として注釈し、基底型の値として使える。

```toml case
id = "subset-ascription-0"
scope = "module"
expect = "accept"
name = "Widen"
parameters = '''A: \Set, S: \Pow A, s: \Cast[A] S'''
```

```ref
\definition value: A := s \of A;
\definition equal: value = s := \refl(s);
```

## 注釈後に subset へ戻す

基底型として注釈した値を、membership の証明なしに subset の値として使うため拒否される。

```toml case
id = "subset-ascription-1"
scope = "module"
expect = "reject"
name = "Narrow"
parameters = '''A: \Set, S: \Pow A, s: \Cast[A] S'''
```

```ref
\definition value: \Cast[A] S := s \of A;
```
