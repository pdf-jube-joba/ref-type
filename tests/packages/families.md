# structure の family と特殊化

## 点に依存する商と関数の外延性

点ごとに特殊化した商を引数型に持つ関数について、型を直接書く場合、関数型の別名を使う場合、局所 module を介す場合に同じ外延性の証明が成立する。

```toml case
id = "pointwise-quotient-function-extensionality"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Quotient(A: \Set, Equivalent: A -> A -> \Prop) {
  \definition ClassOf[x: A]: \Pow A := { y: A \where Equivalent x y };
  \definition Representative[C: \Pow A]: \Set := \Cast[A] ({ x: A \where C = ClassOf x });
  \definition IsClass[C: \Pow A]: \Prop := \exists Representative C;
  \definition Carrier: \Set := \Cast[\Pow A] ({ C: \Pow A \where IsClass C });
}
\module Forms(I: \Set) {
  \structure Space := { Point: \Set, Vector: \Set, };
  \structure Representative[M: Space, x: M.Point]: \Set := {
    point: \Cast[M.Point] ({ y: M.Point \where y = x }),
    vector: M.Vector,
  };
  \module Fiber(M: Space, x: M.Point) {
    \definition Equivalent[a, b: Representative[M, x]]: \Prop := a.vector = b.vector;
    \import \root.Quotient[A := Representative[M, x], Equivalent := Equivalent] \as Q;
    \definition Carrier: \Set := Q.Carrier;
  }
  \definition fiber[M: Space][x: M.Point]: \Set := Fiber[M := M, x := x].Carrier;
  \definition sections[M: Space]: \Set := \forall (x: M.Point) -> (I -> fiber M x) -> M.Vector;
  \definition equal[M: Space][f, g: sections M]: \Prop :=
    \forall (x: M.Point)(v: I -> fiber M x) -> f x v = g x v;
  \definition ext: \forall (M: Space)(f, g: sections M) -> equal M f g -> f = g :=
    \fun (M: Space)(f, g: sections M)(same: equal M f g) =>
      \axiom:funext(f, g, \fun (x: M.Point) => \axiom:funext(f x, g x, same x));

  \definition Function[A, B: \Set]: \Set := A -> B;
  \definition aliased[M: Space]: \Set :=
    \forall (x: M.Point) -> Function (Function I (fiber M x)) M.Vector;
  \definition aliasExt: \forall (M: Space)(f, g: aliased M) -> equal M f g -> f = g := ext;

  \module At(M: Space, x: M.Point) {
    \definition Arguments: \Set := I -> fiber M x;
    \definition Form: \Set := Arguments -> M.Vector;
  }
  \definition scoped[M: Space]: \Set := \forall (x: M.Point) -> At[M := M, x := x].Form;
  \definition copy[M: Space][f: scoped M]: scoped M :=
    \fun (x: M.Point)(v: _) => f x v;
  \definition copyAt[M: Space][f: scoped M]: scoped M :=
    \fun (x: M.Point)(v: At[M := M, x := x].Arguments) => f x v;
  \definition scopedExt: \forall (M: Space)(f, g: scoped M) -> equal M f g -> f = g := ext;
}
```

## temporary field

inline module の引数を特殊化した後、その structure の field を型として使える。

```toml case
id = "module_specialization.temporary-field"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Shapes {
  \structure Space := { Point: \Set, };
}
\module Model(A: \Set) {
  \import \root.Shapes[] \as Shapes;
  \definition space: Shapes.Space := Shapes.Space { Point := A };
}
\module Client(B: \Set, x: B) {
  \definition identity: \root.Model[A := B].space.Point := x;
}
```

## named field

名前を付けた import でも、structure の field は同じ特殊化した型を返す。

```toml case
id = "module_specialization.named-field"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Shapes {
  \structure Space := { Point: \Set, };
}
\module Model(A: \Set) {
  \import \root.Shapes[] \as Shapes;
  \definition space: Shapes.Space := Shapes.Space { Point := A };
}
\module Client(B: \Set, x: B) {
  \import \root.Model[A := B] \as Chosen;
  \definition identity: Chosen.space.Point := x;
}
```

## named piece

親の子 module を import し、選択した index に対する structure の field を使える。

```toml case
id = "module_specialization.named-piece"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Shapes {
  \structure Bundle := { Carrier: \Set };
}
\module Family(I: \Set, types: I -> \Set) {
  \import \root.Shapes[] \as Shapes;
  \module At(i: I) {
    \definition Carrier: \Set := types i;
    \definition bundle: Shapes.Bundle := Shapes.Bundle { Carrier := Carrier };
  }
  \definition bundle[i: I]: Shapes.Bundle := At[i := i].bundle;
  \module Client(j: I, x: types j) {
    \import \parent.At[i := j] \as Piece;
    \definition identity: Piece.bundle.Carrier := x;
  }
}
```

## parameter classifier local namespace

parameter の型に出現する局所 import を、内側の module からも同じ引数で参照できる。

```toml case
id = "module_specialization.parameter-classifier-local-namespace"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Chains {
  \structure Complex := { Carrier: \Set };
  \module Map(C, D: Complex) {
    \structure Data: \Set := { apply: C.Carrier -> D.Carrier };
    \structure Laws[data: Data]: \Prop := { reflexive: \forall (x: C.Carrier) -> data.apply x = data.apply x };
    \definition Map: \Set := \Cast[Data] ({ data: Data \where Laws[data] });
  }
  \module ShortExact(A, B, C: Complex) {
    \import \parent.Map[C := A, D := B] \as Left;
    \import \parent.Map[C := B, D := C] \as Right;
    \structure Data: \Set := { left: Left.Map, right: Right.Map };
    \structure Laws[data: Data]: \Prop := { zero: \forall (x: A.Carrier) -> data.left.apply x = data.left.apply x };
    \definition Sequence: \Set := \Cast[Data] ({data: Data \where Laws[data]});
  }
}
\module Category {
  \import \root.Chains[] \as Chains;
  \module On(Index: \Set, A, B, C: Index -> Chains.Complex,
  sequences: \forall (x: Index) -> Chains.ShortExact[A := A x, B := B x, C := C x].Sequence) {
    \definition leftCarrier[x: Index]: \Set := (A x).Carrier;
    \module At(x, y: Index) {
      \import Chains.Map[C := A x, D := A y] \as Left;
      \import Chains.Map[C := B x, D := B y] \as Middle;
      \import Chains.Map[C := C x, D := C y] \as Right;
      \structure Data: \Set := { left: Left.Map, middle: Middle.Map, right: Right.Map };
    }
  }
}
```

## nested structure alias

structure の中の structure を import の引数に渡し、元の Carrier の値を返せる。

```toml case
id = "module_specialization.nested-structure-alias"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Theory(A: \Set, a: A) {
  \structure Family := { Carrier: \Set, space: Carrier };
  \structure Complex := { family: Family, value: family.Carrier };
  \module Constant(family: Family) {
    \definition complex: Complex := Complex { family := family, value := family.space };
  }
  \module Zero {
    \definition family: Family := Family { Carrier := A, space := a };
    \import \parent.Constant[family := family] \as Constant;
    \definition complex: Complex := Constant.complex;
  }
  \module At(C: Complex) { \definition value: C.family.Carrier := C.family.space; }
}
\module Test {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.Theory[A := Unit, a := Unit::unit] \as T;
  \import T.Zero[] \as Zero;
  \import T.At[C := Zero.complex] \as At;
  \definition result: Unit := At.value;
}
```

## selected namespace classifiers follow carriers and record fields

module の引数に record の Carrier と依存する field を渡し、結果の field 型を利用できる。

```toml case
id = "selected_namespace_classifiers_follow_carriers_and_record_fields"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Structures {
  \structure Topology[Carrier: \Set]: \Set := { openSets: \Pow (\Pow Carrier), };
}
\module Topology(Carrier: \Set) {
  \definition Topology: \Set := \root.Structures[].Topology[Carrier];
  \definition Good[space: Topology]: \Prop := space = space;
}
\module Chart(M: \Set, space: \root.Topology[Carrier := M].Topology) {
  \definition Chart: \Set := M;
}
\module Example {
  \definition ChartType[M: \Set][space: \root.Structures[].Topology[M]]: \Set :=
    \root.Chart[M := M, space := space].Chart;
  \structure Manifold := {
    Point: \Set,
    space: \root.Topology[Carrier := Point].Topology,
    good: \root.Topology[Carrier := Point].Good space,
  };
  \definition manifold[A: \Set][s: \root.Structures[].Topology[A]]: Manifold :=
    Manifold { Point := A, space := s, good := \refl(s) };
  \definition identity[A: \Set][s: \root.Structures[].Topology[A]][x: A]:
    (manifold A s).Point := x;
}
```

## selected namespace functions preserve degree under lambdas

lambda の局所 index で特殊化した関数は、その index の subset を受け取り返す。

```toml case
id = "selected_namespace_functions_preserve_degree_under_lambdas"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
  \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
  \module At(n: Nat) {
    \definition Carrier: \Set := \Cast[Nat] ({ k: Nat \where k = n });
    \definition identity[x: Carrier]: Carrier := x;
  }
  \definition apply[n: Nat][x: At[n := n].Carrier]: At[n := n].Carrier :=
    At[n := n].identity x;
  \definition underLambda: \forall (n: Nat) -> At[n := n].Carrier -> At[n := n].Carrier :=
    \fun (n: Nat) (x: At[n := n].Carrier) => At[n := n].identity x;
}
```

## structure families preserve nested named import arguments

子から親の別の子を import しても、family の index は元の引数に対応する。

```toml case
id = "structure_families_preserve_nested_named_import_arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Shapes { \structure Bundle := { Carrier: \Set, }; }
\module Family(I: \Set, types: I -> \Set) {
  \import \root.Shapes[] \as Shapes;
  \module At(i: I) {
    \definition Carrier: \Set := types i;
    \definition bundle: Shapes.Bundle := Shapes.Bundle { Carrier := Carrier };
  }
  \module From(i: I) {
    \import \parent.At[i := i] \as Chosen;
    \definition bundle: Shapes.Bundle := Chosen.bundle;
  }
  \definition bundle[i: I]: Shapes.Bundle := From[i := i].bundle;
}
\module Consumer(J: \Set, family: J -> \Set) {
  \import \root.Family[I := J, types := family] \as F;
  \definition identity[j: J][x: family j]: (F.bundle j).Carrier := x;
}
```

## degree indexed structure results preserve declaration arguments

index を successor に進めた結果の structure を返し、その演算の等式を証明できる。

```toml case
id = "degree_indexed_structure_results_preserve_declaration_arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro(A: \Set) {
  \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
  \structure Operator[k: Nat] := { apply: A -> A, };
  \module At(k: Nat) {
    \definition step[previous: Operator[k]]: Operator[Nat::succ k] :=
      Operator[Nat::succ k] { apply := previous.apply };
  }
  \definition step[k: Nat][previous: Operator[k]]: Operator[Nat::succ k] :=
    At[k := k].step previous;
  \definition identity[k: Nat][x: A]: (step k (Operator[k] {
    apply := \fun (y: A) => y,
  })).apply x = x := \refl(x);
}
```

## 入れ子の family の guard

family の space と Data は、同じ親の型引数と complex を使って構成される。

```toml case
id = "nested-family-guards"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := R].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
  }
}
```

## 入れ子の family の環境違い

R 上の factory に S 上の complex を渡している。

```toml case
id = "nested-family-ambient-mismatch"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R, S: \Set) {
  \import \root.Chains[R := S] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := S].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
  }
}
```

## 環境と独立した index

固定した Index の family にも、親の R に対応した space の guard が適用される。

```toml case
id = "fixed-family-index"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Indices { \inductive Index: \Set := | point: Index; }
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) { \import \root.Indices[] \as Indices;
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: Indices.Index -> \Set,
    space: \forall (n: Indices.Index) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
}
\module Resolutions(R: \Set) { \import \root.Indices[] \as Indices;
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: Indices.Index) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := R].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
  }
}
```

## 固定 index の環境違い

index が同じでも親の space の環境は R と S で異なる。

```toml case
id = "fixed-family-ambient-mismatch"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Indices { \inductive Index: \Set := | point: Index; }
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) { \import \root.Indices[] \as Indices;
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: Indices.Index -> \Set,
    space: \forall (n: Indices.Index) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
}
\module Resolutions(R: \Set) { \import \root.Indices[] \as Indices;
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: Indices.Index) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R, S: \Set) {
  \import \root.Chains[R := S] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := S].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
  }
}
```

## imported factory fields can be projected after specialization

特殊化した sequence の field を、元の complex に依存する Data 型として取り出せる。

```toml case
id = "imported_factory_fields_can_be_projected_after_specialization"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := R].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
    \definition recovered: \root.Resolutions[R := R].Of[P := P].Data := sequence.data;
  }
}
```

## imported factory specializes a structure dependent type alias

complex を引数に持つ type alias を、特殊化した factory の field と引数の型に使える。

```toml case
id = "imported_factory_specializes_a_structure_dependent_type_alias"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
  \module Pair(A, B: Complex) {
    \definition Data: \Set := \forall (n: R) -> A.family.Carrier n -> B.family.Carrier n;
  }
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \definition ChainData[P, Q: Chains.Complex]: \Set := \root.Chains[R := R].Pair[A := P, B := Q].Data;
    \structure Sequence := {
      complex: Chains.Complex,
      data: ChainData complex complex,
    };
    \definition make[P: Chains.Complex][p: ChainData P P]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: Chains.Pair[A := P, B := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
  }
}
```

## 依存する type alias の環境違い

別の親引数から作った complex を type alias の引数に渡している。

```toml case
id = "dependent-alias-mismatch"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
  \module Pair(A, B: Complex) {
    \definition Data: \Set := \forall (n: R) -> A.family.Carrier n -> B.family.Carrier n;
  }
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \definition ChainData[P, Q: Chains.Complex]: \Set := \root.Chains[R := R].Pair[A := P, B := Q].Data;
    \structure Sequence := {
      complex: Chains.Complex,
      data: ChainData complex complex,
    };
    \definition make[P: Chains.Complex][p: ChainData P P]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R, S: \Set) {
  \import \root.Chains[R := S] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: Chains.Pair[A := P, B := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
  }
}
```

## specialized factory fields can be record type arguments

再構成した family を record の型引数に渡し、同じ Carrier の値で構築できる。

```toml case
id = "specialized_factory_fields_can_be_record_type_arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
  \structure Data[family: Family]: \Set := { read: \forall (n: R) -> family.Carrier n };
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \definition makeFamily[P: Chains.Complex]: Chains.Family := Chains.Family {
      Carrier := P.family.Carrier, space := P.family.space,
    };
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := R].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
    \definition data: Chains.Data[Sequences.makeFamily P] := Chains.Data[Sequences.makeFamily P] { read := p };
  }
}
```

## specialized factory fields can be module arguments

再構成した family を別 module の引数に渡し、元と同じ Data 型を使える。

```toml case
id = "specialized_factory_fields_can_be_module_arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Space[V: \Set]: \Set := R -> V;
  \structure Bundle := { Carrier: \Set, space: Space Carrier };
}
\module Chains(R: \Set) {
  \import \root.Base[R := R] \as Modules;
  \structure Family := {
    Carrier: R -> \Set,
    space: \forall (n: R) -> Modules.Space (Carrier n),
  };
  \structure Complex := { family: Family };
  \module Consume(family: Family) {
    \definition Data: \Set := \forall (n: R) -> family.Carrier n;
  }
}
\module Resolutions(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \module Of(P: Chains.Complex) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Sequences {
    \import \root.Resolutions[R := R] \as Resolutions;
    \definition makeFamily[P: Chains.Complex]: Chains.Family := Chains.Family {
      Carrier := P.family.Carrier, space := P.family.space,
    };
    \structure Sequence := {
      complex: Chains.Complex,
      data: Resolutions.Of[P := complex].Data,
    };
    \definition make[P: Chains.Complex][p: Resolutions.Of[P := P].Data]: Sequence :=
      Sequence { complex := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Chains[R := R] \as Chains;
  \import \root.Resolutions[R := R].Sequences[] \as Sequences;
  \module Of(P: Chains.Complex, p: \root.Resolutions[R := R].Of[P := P].Data) {
    \definition sequence: Sequences.Sequence := Sequences.make P p;
    \import Chains.Consume[family := Sequences.makeFamily P] \as Consumed;
    \definition data: Consumed.Data := p;
  }
}
```

## 異なる family index と局所 binder

j と k の Carrier はそれぞれの index に対応し、局所 binder からも同じ規則で特殊化される。

```toml case
id = "distinct-family-indices"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Shapes {
  \structure Bundle := { Carrier: \Set, };
}
\module Family(I: \Set, types: I -> \Set) {
  \import \root.Shapes[] \as Shapes;
  \module At(i: I) {
    \definition Carrier: \Set := types i;
    \definition bundle: Shapes.Bundle := Shapes.Bundle { Carrier := Carrier };
  }
  \definition bundle[i: I]: Shapes.Bundle := At[i := i].bundle;
  \module Client(j, k: I, x: types j, y: types k) {
    \definition left: (bundle j).Carrier := x;
    \definition right: (bundle k).Carrier := y;
    \definition local[i: I][value: types i]: (bundle i).Carrier := value;
    \definition underLambda: \forall (i: I) -> (bundle i).Carrier -> types i :=
      \fun (i: I) (value: (bundle i).Carrier) => value;
  }
}
\module Consumer(J: \Set, family: J -> \Set) {
  \import \root.Family[I := J, types := family] \as F;
  \definition identity[j: J][x: family j]: (F.bundle j).Carrier := x;
}
```

## 異なる family index の混用

k の Carrier を要求する位置に j の Carrier の値を渡す。

```toml case
id = "wrong-family-index"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Shapes {
  \structure Bundle := { Carrier: \Set, };
}
\module Family(I: \Set, types: I -> \Set) {
  \import \root.Shapes[] \as Shapes;
  \module At(i: I) {
    \definition Carrier: \Set := types i;
    \definition bundle: Shapes.Bundle := Shapes.Bundle { Carrier := Carrier };
  }
  \definition bundle[i: I]: Shapes.Bundle := At[i := i].bundle;
  \module Client(j, k: I, x: types j, y: types k) {
    \definition left: (bundle j).Carrier := x;
    \definition right: (bundle k).Carrier := x;
    \definition local[i: I][value: types i]: (bundle i).Carrier := value;
    \definition underLambda: \forall (i: I) -> (bundle i).Carrier -> types i :=
      \fun (i: I) (value: (bundle i).Carrier) => value;
  }
}
\module Consumer(J: \Set, family: J -> \Set) {
  \import \root.Family[I := J, types := family] \as F;
  \definition identity[j: J][x: family j]: (F.bundle j).Carrier := x;
}
```
