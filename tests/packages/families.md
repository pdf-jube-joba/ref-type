# Structure families and specialization

## Point-dependent quotients and function extensionality

For functions whose argument types are point-specialized quotients, the same extensionality proof works with an explicit type, a function-type alias, or a local module.

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

After specializing inline module arguments, the structure's fields can be used as types.

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

Named imports also return the same specialized types through structure fields.

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

A parent's child module can be imported to use structure fields at a selected index.

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

A local import appearing in a parameter type can be referenced with the same arguments from an inner module.

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

A structure nested within a structure can be passed as an import argument to return a value of the original Carrier.

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

A record's Carrier and dependent fields can be passed as module arguments, making the resulting field type available.

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

A function specialized at a lambda's local index accepts and returns the subset at that index.

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

Importing another child of the parent from a child preserves the family's original index arguments.

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

A structure at the successor index can be returned and its operation's equality proved.

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

## Nested family guards

A family's space and Data are constructed using the same parent type argument and complex.

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

## Nested families with different environments

A complex over S is passed to a factory over R.

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

## Environment-independent indices

A family over a fixed Index also applies the space guard corresponding to the parent's R.

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

## Fixed indices with different environments

Even with the same index, the parent space environments differ between R and S.

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

Fields of a specialized sequence can be extracted with the Data type depending on the original complex.

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

A type alias taking a complex can be used in the field and argument types of a specialized factory.

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

## Dependent type aliases with different environments

A complex created from different parent arguments is passed as a type-alias argument.

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

A reconstructed family can be passed as a record type argument and constructed with a value of the same Carrier.

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

A reconstructed family can be passed to another module, preserving the original Data type.

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

## Different family indices and local binders

The Carriers at j and k correspond to their respective indices and specialize by the same rules under local binders.

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

## Mixing different family indices

A value of the Carrier at j is passed where the Carrier at k is required.

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
