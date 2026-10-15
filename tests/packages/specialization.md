# module の特殊化

## 親引数の入れ替え

親 module の型引数を入れ替えても、子の型 alias は対応する引数で一度だけ置換される。

```toml case
id = "child_type_aliases_substitute_overlapping_parent_arguments_once"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Maps(A, B: \Set) {
  \definition Source: \Set := \Pow A;
  \definition Target: \Set := \Pow B;
  \module At(U: Source, V: Target) {}
  \module After(C: \Set) {
    \import \root.Maps[A := B, B := C] \as Next;
    \module On(V: Target, W: \Pow C) {
      \import Next.At[U := V, V := W] \as Applied;
    }
  }
}
```

## 依存する signature の guard

生成した bundle と元の bundle の Carrier が一致し、親の型引数を保った証明を利用できる。

```toml case
id = "explicit_guards_preserve_parent_arguments_in_dependent_signatures"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \structure Law[V: \Set]: \Set { apply: R -> V }
  \definition Space(V: \Set): \Set := Law[V];
  \structure Bundle { Carrier: \Set, space: Space Carrier }
  \module Take(B: Bundle) {}
  \definition MapBetween(A, B: Bundle): \Set := A.Carrier -> B.Carrier;
  \definition Property(A, B: Bundle)(f: MapBetween A B): \Prop := \forall (x: B.Carrier) -> x = x;
}
\module Wrapper(R: \Set) {
  \import \root.Base[R := R] \as B;
  \inductive Unit: \Set := | unit: Unit;
  \module At(M: B.Bundle) {
    \module Slot(n: Unit) {
      \definition Carrier: \Set := M.Carrier;
      \definition space: B.Space Carrier := M.space;
    }
    \definition Carrier(n: Unit): \Set := Slot[n := n].Carrier;
    \definition space(n: Unit): B.Space (Carrier n) := Slot[n := n].space;
    \definition bundle(n: Unit): B.Bundle := B.Bundle { Carrier := Carrier n, space := space n };
    \definition proof: B.Property (bundle Unit::unit) M (\fun (x: M.Carrier) => x) := \fun (y: Carrier Unit::unit) => \refl(y);
  }
}
\module Consumer(S: \Set) {
  \import \root.Base[R := S] \as B;
  \import \root.Wrapper[R := S] \as W;
  \module At(M: B.Bundle) {
    \import W.At[M := M] \as A;
    \import B.Take[B := A.bundle W.Unit::unit] \as Taken;
    \definition proof: _ := A.proof;
  }
}
```

## 異なる環境での bundle

各 bundle の space は、それぞれを生成した module の環境の型に合っている。

```toml case
id = "specialized_bundle_arguments_keep_inline_module_checks_in_the_instance"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space(V: \Set): \Set := R -> V;
  \structure Bundle { Carrier: \Set, space: Space Carrier }
  \module Hom(V, W: \Set, source: Space V, target: Space W) {
    \definition Map: \Set := V -> W;
  }
  \definition Maps(A, B: Bundle): \Set :=
    Hom[V := A.Carrier, W := B.Carrier, source := A.space, target := B.space].Map;
  \module Free(S: \Set, seed: S) {
    \definition space: Space S := \fun (r: R) => seed;
    \definition bundle: Bundle := Bundle { Carrier := S, space := space };
  }
}
\module Native {
  \inductive Unit: \Set := | unit: Unit;
  \inductive Two: \Set := | left: Two | right: Two;
  \import \root.Base[R := Unit] \as B;
  \import B.Free[S := Unit, seed := Unit::unit] \as F;
  \definition identity: B.Maps F.bundle F.bundle := \fun (x: Unit) => x;
  \import \root.Base[R := Two] \as Other;
  \import Other.Free[S := Unit, seed := Unit::unit] \as G;
  \definition otherIdentity: Other.Maps G.bundle G.bundle := \fun (x: Unit) => x;
}
```

## 環境が異なる bundle の混用

Unit 上で生成した bundle を Two 上の Maps に渡すため拒否される。

```toml case
id = "specialized_bundle_guards_reject_a_different_ambient_type"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space(V: \Set): \Set := R -> V;
  \structure Bundle { Carrier: \Set, space: Space Carrier }
  \module Hom(V, W: \Set, source: Space V, target: Space W) {
    \definition Map: \Set := V -> W;
  }
  \definition Maps(A, B: Bundle): \Set :=
    Hom[V := A.Carrier, W := B.Carrier, source := A.space, target := B.space].Map;
}
\module Native {
  \inductive Unit: \Set := | unit: Unit;
  \inductive Two: \Set := | left: Two | right: Two;
  \import \root.Base[R := Unit] \as B;
  \import \root.Base[R := Two] \as Other;
  \definition bundle: B.Bundle := B.Bundle {
    Carrier := Unit, space := \fun (x: Unit) => x,
  };
  \definition wrong: Other.Maps bundle bundle := \fun (x: Unit) => x;
}
```

## 子同士の推移的な依存

Derived から Specification を経て Basic に到達し、返された値を同じ Nat として扱える。

```toml case
id = "nested_namespaces_follow_module_dependency_order"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Parent {
  \inductive Nat: \VType := | zero: Nat;
  \module Operation {
    \module Basic {
      \definition zero: Nat := Nat::zero;
    }
    \module Derived {
      \import \root.Parent[].Law[].Specification[] \as S;
      \definition zero: Nat := S.zero;
    }
  }
  \module Law {
    \module Specification {
      \import \root.Parent[].Operation[].Basic[] \as B;
      \definition zero: Nat := B.zero;
    }
  }
}
\module Consumer {
  \import \root.Parent[] \as P;
  \import P.Operation[].Derived[] \as D;
  \check D.zero: P.Nat;
  \definition zeroMatches: D.zero^ = P.Nat^::zero := \refl(P.Nat^::zero);
}
```

## 親の import に依存する子引数

親が import した record の値を子の引数に渡し、その field を利用できる。

```toml case
id = "nested_module_arguments_specialize_parent_imported_types"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Top(A: \Set) { \structure T: \Set { x: A } }
\module Parent(A: \Set) {
  \import \root.Top[A := A] \as Base;
  \module Child(value: Base.T) { \definition get: A := #x{value}; }
}
\module Test {
  \inductive Point: \Set := | point: Point;
  \import \root.Top[A := Point] \as Top;
  \definition x: Top.T := Top.T { x := Point::point };
  \import \root.Parent[A := Point].Child[value := x] \as C;
  \definition result: C.get = Point::point := \refl(Point::point);
}
```

## 局所変数を含む特殊化と閉じた import

局所引数を持つ参照の後でも、閉じた import の恒等関数は局所変数に依存しない。

```toml case
id = "closed_namespace_does_not_reuse_a_convertible_local_specialization"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Template(V: \Set) {
  \definition Carrier: \Set := V;
  \module Universal(U: \Set) {
    \definition Map: \Set := Carrier -> U;
  }
}
\module Consumer(A: \Set) {
  \definition family(x: A): \Set := A;
  \definition local(x: A): \Set := \root.Template[V := family x].Carrier;
  \import \root.Template[V := A] \as Closed;
  \import Closed.Universal[U := Closed.Carrier] \as Universal;
  \definition identity: Universal.Map := \fun (x: A) => x;
}
```

## 入れ子の Carrier alias

同じ Carrier から特殊化した Source と Target の値は、alias を経ても同じ型として使える。

```toml case
id = "carrier_aliases_keep_their_identity_across_nested_specializations"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Types(A: \Set) { \structure T: \Set { x: A } }
\module Pair(A, B: \Set) { \structure P: \Set { first: A, second: B } }
\module Product(A, B: \Set) {
  \import \root.Pair[A := A, B := B] \as P;
  \definition Carrier: \Set := P.P;
  \import \root.Types[A := Carrier] \as Top;
  \module Universal(X: \Set) {
    \import \root.Types[A := X] \as Source;
    \definition Source: \Set := Source.T;
    \definition Target: \Set := Top.T;
    \definition identity(source: Source) (target: Target): X -> Carrier -> \Prop := \fun (x: X) (y: Carrier) => #x{source} = x;
  }
}
\module Complex {
  \inductive Real: \Set := | zero: Real;
  \import \root.Product[A := Real, B := Real] \as Product;
  \definition Carrier: \Set := Product.Carrier;
  \module Functions(A: \Set) {
    \import Product.Universal[X := A] \as Into;
    \definition Source: \Set := Into.Source;
    \definition Target: \Set := Into.Target;
    \definition apply(source: Source) (target: Target): A -> Carrier -> \Prop := Into.identity source target;
  }
}
\module Consumer {
  \import \root.Complex[] \as Complex;
  \import Complex.Functions[A := Complex.Carrier] \as Functions;
  \definition same(x: Functions.Source): Functions.Target := x;
}
```

## 再帰 binder の後の型引数

successor 分岐の型引数は、その分岐で束縛した n に対応する。

```toml case
id = "indexed_constructors_check_module_types_after_recursive_binders"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Natural {
  \inductive Nat: \Set := | zero: Nat | successor: Nat -> Nat;
}
\module Construction {
  \import \root.Natural[] \as Nat;
  \module At(n: Nat.Nat) {
    \structure Data: \Set { value: Nat.Nat }
    \definition Map: \Set := Data;
  }
  \inductive Stage: \forall (n: Nat.Nat) -> \Set :=
    | zero: At[n := Nat.Nat::zero].Map -> Stage Nat.Nat::zero
  | successor: \forall (n: Nat.Nat) -> Stage n ->
    At[n := Nat.Nat::successor n].Map -> Stage (Nat.Nat::successor n);
  \definition current: \forall (n: Nat.Nat) -> Stage n -> At[n := n].Map :=
    \induction (n: Nat.Nat)(stage: Stage n) \return At[n := n].Map \with {
    | zero: \fun (g: At[n := Nat.Nat::zero].Map) => g
    | successor: \fun (n: Nat.Nat)(stage: Stage n)(before: At[n := n].Map)
    (g: At[n := Nat.Nat::successor n].Map) => g
  };
}
```

## 依存する family の再公開

直接参照と Outer を経た参照は、同じ n と point に対する Carrier を返す。

```toml case
id = "reexported_dependent_families_compose_enclosing_arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Numbers {
  \inductive N: \VType := | zero: N | succ: N -> N;
}
\module Source(n: \root.Numbers[].N^) {
  \definition Index: \Set := \Cast[\root.Numbers[].N^] ({ i: \root.Numbers[].N^ \where i = n });
  \structure Family { Carrier: Index -> \Set }
  \module Slot(i: Index) { \definition Carrier: \Set := \root.Numbers[].N^; }
  \definition family: Family := Family { Carrier := \fun (i: Index) => Slot[i := i].Carrier };
}
\module Outer(n: \root.Numbers[].N^) {
  \import \root.Source[n := n] \as Source;
  \definition family: Source.Family := Source.family;
}
\module Consumer {
  \definition one: \root.Numbers[].N^ := \root.Numbers[].N^::succ \root.Numbers[].N^::zero;
  \import \root.Source[n := one] \as Source;
  \definition point: Source.Index := \into[\root.Numbers[].N^](one, { i: \root.Numbers[].N^ \where i = one }) \by { \refl(one) };
  \definition Direct: \Set := #Carrier{Source.family} point;
  \definition direct: Direct := one;
  \import \root.Outer[n := one] \as Outer;
  \definition Reexported: \Set := #Carrier{Outer.family} point;
  \definition reexported: Reexported := one;
}
```

## inline structure / valid

引数 x は指定した A の値なので、生成した structure の field を使える。

```toml case
id = "inline-structure-valid"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Shapes {
  \structure Packed { A: \Set, value: A }
}
\module Factory(A: \Set, x: A) {
  \import \root.Shapes[] \as Shapes;
  \definition packed: Shapes.Packed := Shapes.Packed { A := A, value := x };
}
\module Client {
  \import \root.Shapes[] \as Shapes;
  \inductive Unit: \Set := | unit: Unit;
  \definition make(A: \Set)(x: A): Shapes.Packed :=
    \root.Factory[A := A, x := x].packed;
  \definition packed: Shapes.Packed :=
    \root.Factory[A := Unit, x := Unit::unit].packed;
  \definition value: Unit := packed.value;
  \definition law: value = Unit::unit := \refl(value);
}
```

## inline structure / invalid

Unit の値を渡す位置に集合の sort を渡しているため拒否される。

```toml case
id = "inline-structure-invalid"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Shapes {
  \structure Packed { A: \Set, value: A }
}
\module Factory(A: \Set, x: A) {
  \import \root.Shapes[] \as Shapes;
  \definition packed: Shapes.Packed := Shapes.Packed { A := A, value := x };
}
\module Client {
  \import \root.Shapes[] \as Shapes;
  \inductive Unit: \Set := | unit: Unit;
  \definition make(A: \Set)(x: A): Shapes.Packed :=
    \root.Factory[A := A, x := x].packed;
  \definition packed: Shapes.Packed :=
    \root.Factory[A := Unit, x := \Set].packed;
  \definition value: Unit := packed.value;
  \definition law: value = Unit::unit := \refl(value);
}
```

## 異なる型の module 引数

A の値を要求する module に B の値を渡すため拒否される。

```toml case
id = "direct-argument-0"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Family(A: \Set, B: \Set) {
  \module At(x: A) { \definition value: A := x; }
  \definition invalid(y: B): A := At[x := y].value;
}
```

## module 引数に依存する証明

y と x の等式を要求する位置に y と y の等式を渡すため拒否される。

```toml case
id = "direct-argument-1"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Family(A: \Set) {
  \module At(x: A) {
    \definition value(y: A)(proof: y = x): A := y;
  }
  \definition invalid(x, y: A): A := At[x := x].value y (\refl(y));
}
```

## temporary program datatypes and reflections agree

局所 module の Program 帰納型の特殊化と reflection は、同じ引数に対応する型と値を返す。

```toml case
id = "temporary_program_datatypes_and_reflections_agree"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module M {
  \inductive Unit: \VType := | unit: Unit;
  \module Family(A: \VType) { \inductive Box: \VType := | box: A -> Box; }
  \definition make(x: Unit): \F(Family[A := Unit].Box) := \return Family[A := Unit].Box::box x;
  \definition reflected(x: Unit^): Family[A := Unit].Box^ := make^ x;
}
```

## temporary modules preserve case branch binders

case branch の binder を引数に使って局所 module を特殊化し、その branch の型に合う値を返せる。

```toml case
id = "temporary_modules_preserve_case_branch_binders"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module M {
  \inductive Unit: \VType := | unit: Unit;
  \inductive Box: \VType := | box: Unit -> Box;
  \module Value(x: Unit) { \definition value: Unit := x; }
  \definition get(x: Box): \F(Unit) := \match x \in Box \with {
    | box y : \return Value[x := y].value
  };
}
```

## temporary modules follow inferred lambda binders

lambda の binder の型が推論された後でも、その局所変数を module 引数として渡せる。

```toml case
id = "temporary_modules_follow_inferred_lambda_binders"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module M {
  \module Family(A: \Set) { \inductive Box: \Set := | box: A -> Box; }
  \definition make: \forall (A: \Set) -> A -> Family[A := A].Box :=
    \fun (A: _) (x: _) => Family[A := A].Box::box x;
}
```
