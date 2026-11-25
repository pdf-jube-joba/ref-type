# Structure families and specialization

## Function extensionality over specialized refinements

For functions whose argument types are point-specialized quotients, the same extensionality proof works with an explicit type, a function-type alias, or a local module.

```toml case
id = "extensionality-over-specialized-refinements"
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
\module IndexedFunctions(I: \Set) {
  \structure Family := { Index: \Set, Value: \Set, };
  \structure Representative[M: Family, x: M.Index]: \Set := {
    index: \Cast[M.Index] ({ y: M.Index \where y = x }),
    value: M.Value,
  };
  \module AtIndex(M: Family, x: M.Index) {
    \definition Equivalent[a, b: Representative[M, x]]: \Prop := a.value = b.value;
    \import \root.Quotient[A := Representative[M, x], Equivalent := Equivalent] \as Q;
    \definition Carrier: \Set := Q.Carrier;
  }
  \definition Selected[M: Family][x: M.Index]: \Set := AtIndex[M := M, x := x].Carrier;
  \definition Functions[M: Family]: \Set := \forall (x: M.Index) -> (I -> Selected M x) -> M.Value;
  \definition Pointwise[M: Family][f, g: Functions M]: \Prop :=
    \forall (x: M.Index)(v: I -> Selected M x) -> f x v = g x v;
  \definition ext: \forall (M: Family)(f, g: Functions M) -> Pointwise M f g -> f = g :=
    \fun (M: Family)(f, g: Functions M)(same: Pointwise M f g) =>
      \axiom:funext(f, g, \fun (x: M.Index) => \axiom:funext(f x, g x, same x));

  \definition Function[A, B: \Set]: \Set := A -> B;
  \definition aliased[M: Family]: \Set :=
    \forall (x: M.Index) -> Function (Function I (Selected M x)) M.Value;
  \definition aliasExt: \forall (M: Family)(f, g: aliased M) -> Pointwise M f g -> f = g := ext;

  \module At(M: Family, x: M.Index) {
    \definition Arguments: \Set := I -> Selected M x;
    \definition Function: \Set := Arguments -> M.Value;
  }
  \definition scoped[M: Family]: \Set := \forall (x: M.Index) -> At[M := M, x := x].Function;
  \definition copy[M: Family][f: scoped M]: scoped M :=
    \fun (x: M.Index)(v: _) => f x v;
  \definition copyAt[M: Family][f: scoped M]: scoped M :=
    \fun (x: M.Index)(v: At[M := M, x := x].Arguments) => f x v;
  \definition scopedExt: \forall (M: Family)(f, g: scoped M) -> Pointwise M f g -> f = g := ext;
}
```

## Field types from direct module instantiation

After specializing inline module arguments, the structure's fields can be used as types.

```toml case
id = "direct-instantiation-field-type"
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

## Field types from named imports

Named imports also return the same specialized types through structure fields.

```toml case
id = "imported-instantiation-field-type"
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

## Field types from indexed child imports

A parent's child module can be imported to use structure fields at a selected index.

```toml case
id = "indexed-child-import-field-type"
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

## Parameterized types remain valid in inner module imports

A local import appearing in a parameter type can be referenced with the same arguments from an inner module.

```toml case
id = "parameter-types-and-inner-module-imports"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Mappings {
  \structure Carrier := { Carrier: \Set };
  \module Map(C, D: Carrier) {
    \structure Data: \Set := { apply: C.Carrier -> D.Carrier };
    \structure Laws[data: Data]: \Prop := { reflexive: \forall (x: C.Carrier) -> data.apply x = data.apply x };
    \definition Map: \Set := \Cast[Data] ({ data: Data \where Laws[data] });
  }
  \module Composable(A, B, C: Carrier) {
    \import \parent.Map[C := A, D := B] \as Left;
    \import \parent.Map[C := B, D := C] \as Right;
    \structure Data: \Set := { left: Left.Map, right: Right.Map };
    \structure Laws[data: Data]: \Prop := { same: \forall (x: A.Carrier) -> data.left.apply x = data.left.apply x };
    \definition Pair: \Set := \Cast[Data] ({data: Data \where Laws[data]});
  }
}
\module IndexedMappings {
  \import \root.Mappings[] \as Mappings;
  \module On(Index: \Set, A, B, C: Index -> Mappings.Carrier,
  sequences: \forall (x: Index) -> Mappings.Composable[A := A x, B := B x, C := C x].Pair) {
    \definition leftCarrier[x: Index]: \Set := (A x).Carrier;
    \module At(x, y: Index) {
      \import Mappings.Map[C := A x, D := A y] \as Left;
      \import Mappings.Map[C := B x, D := B y] \as Middle;
      \import Mappings.Map[C := C x, D := C y] \as Right;
      \structure Data: \Set := { left: Left.Map, middle: Middle.Map, right: Right.Map };
    }
  }
}
```

## Nested structure alias

A structure nested within a structure can be passed as an import argument to return a value of the original Carrier.

```toml case
id = "nested-structure-alias"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module NestedStructures(A: \Set, a: A) {
  \structure Family := { Carrier: \Set, seed: Carrier };
  \structure Package := { family: Family, value: family.Carrier };
  \module Constant(family: Family) {
    \definition package: Package := Package { family := family, value := family.seed };
  }
  \module Seed {
    \definition family: Family := Family { Carrier := A, seed := a };
    \import \parent.Constant[family := family] \as Constant;
    \definition package: Package := Constant.package;
  }
  \module At(C: Package) {
    \definition value: C.family.Carrier := C.family.seed;
  }
}
\module Test {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.NestedStructures[A := Unit, a := Unit::unit] \as T;
  \import T.Seed[] \as Seed;
  \import T.At[C := Seed.package] \as At;
  \definition result: Unit := At.value;
}
```

## Selected types depend on record fields

A record's Carrier and dependent fields can be passed as module arguments, making the resulting field type available.

```toml case
id = "selected-types-depend-on-record-fields"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Structures {
  \structure Selection[Carrier: \Set]: \Set := { members: \Pow Carrier, };
}
\module Selection(Carrier: \Set) {
  \definition Selection: \Set := \root.Structures[].Selection[Carrier];
  \definition Good[selection: Selection]: \Prop := selection = selection;
}
\module View(M: \Set, selection: \root.Selection[Carrier := M].Selection) {
  \definition View: \Set := M;
}
\module Example {
  \definition ViewedType[M: \Set][selection: \root.Structures[].Selection[M]]: \Set :=
    \root.View[M := M, selection := selection].View;
  \structure Bundle := {
    Carrier: \Set,
    selection: \root.Selection[Carrier := Carrier].Selection,
    good: \root.Selection[Carrier := Carrier].Good selection,
  };
  \definition bundle[A: \Set][s: \root.Structures[].Selection[A]]: Bundle :=
    Bundle { Carrier := A, selection := s, good := \refl(s) };
  \definition identity[A: \Set][s: \root.Structures[].Selection[A]][x: A]:
    (bundle A s).Carrier := x;
}
```

## Specialized functions preserve lambda-bound indices

A function specialized at a lambda's local index accepts and returns the subset at that index.

```toml case
id = "local-indices-in-specialized-functions"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module LocalIndicesInSpecializedFunctions {
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

## Structure families preserve nested named import arguments

Importing another child of the parent from a child preserves the family's original index arguments.

```toml case
id = "structure-families-preserve-nested-named-import-arguments"
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

## Indexed structure results preserve declaration arguments

A structure at the successor index can be returned and its operation's equality proved.

```toml case
id = "indexed-structure-results-preserve-arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module IndexedStructureResultsPreserveArguments(A: \Set) {
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

The packed family's dependent data type uses the same outer type argument as its family group.

```toml case
id = "nested-family-guards"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := R].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
  }
}
```

## Nested families with different environments

A group over S is passed to a factory over R.

```toml case
id = "nested-family-ambient-mismatch"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R, S: \Set) {
  \import \root.Families[R := S] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := S].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
  }
}
```

## Environment-independent indices

A family over a fixed Index still requires function fields of type R -> Carrier at each index.

```toml case
id = "fixed-family-index"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Indices {
  \inductive Index: \Set := | point: Index;
}
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Indices[] \as Indices;
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: Indices.Index -> \Set,
    maps: \forall (n: Indices.Index) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
}
\module Readers(R: \Set) {
  \import \root.Indices[] \as Indices;
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: Indices.Index) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := R].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
  }
}
```

## Fixed indices with different environments

Even with a fixed index type, families instantiated with R and S retain different required function field types.

```toml case
id = "fixed-family-ambient-mismatch"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Indices {
  \inductive Index: \Set := | point: Index;
}
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Indices[] \as Indices;
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: Indices.Index -> \Set,
    maps: \forall (n: Indices.Index) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
}
\module Readers(R: \Set) {
  \import \root.Indices[] \as Indices;
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: Indices.Index) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R, S: \Set) {
  \import \root.Families[R := S] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := S].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
  }
}
```

## Imported factory fields can be projected after specialization

Projecting a packed family's data field preserves the type determined by its family group.

```toml case
id = "imported-factory-fields-can-be-projected-after-specialization"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := R].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
    \definition recovered: \root.Readers[R := R].Of[P := P].Data := sequence.data;
  }
}
```

## Imported factory specializes a structure dependent type alias

A type alias taking a family group can be used in the field and argument types of a specialized factory.

```toml case
id = "imported-factory-specializes-a-structure-dependent-type-alias"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
  \module Pair(A, B: FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> A.family.Carrier n -> B.family.Carrier n;
  }
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \definition MapType[P, Q: Families.FamilyGroup]: \Set := \root.Families[R := R].Pair[A := P, B := Q].Data;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: MapType group group,
    };
    \definition make[P: Families.FamilyGroup][p: MapType P P]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: Families.Pair[A := P, B := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
  }
}
```

## Dependent type aliases with different environments

A family group created from different outer arguments is passed as a type-alias argument.

```toml case
id = "dependent-alias-mismatch"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
  \module Pair(A, B: FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> A.family.Carrier n -> B.family.Carrier n;
  }
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \definition MapType[P, Q: Families.FamilyGroup]: \Set := \root.Families[R := R].Pair[A := P, B := Q].Data;
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: MapType group group,
    };
    \definition make[P: Families.FamilyGroup][p: MapType P P]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R, S: \Set) {
  \import \root.Families[R := S] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: Families.Pair[A := P, B := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
  }
}
```

## Specialized factory fields can be record type arguments

A reconstructed family can be passed as a record type argument and constructed with a value of the same Carrier.

```toml case
id = "specialized-factory-fields-can-be-record-type-arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
  \structure Data[family: Family]: \Set := { read: \forall (n: R) -> family.Carrier n };
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \definition makeFamily[P: Families.FamilyGroup]: Families.Family := Families.Family {
      Carrier := P.family.Carrier, maps := P.family.maps,
    };
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := R].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
    \definition data: Families.Data[Packing.makeFamily P] := Families.Data[Packing.makeFamily P] { read := p };
  }
}
```

## Specialized factory fields can be module arguments

A reconstructed family can be passed to another module, preserving the original Data type.

```toml case
id = "specialized-factory-fields-can-be-module-arguments"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base(R: \Set) {
  \definition Maps[V: \Set]: \Set := R -> V;
}
\module Families(R: \Set) {
  \import \root.Base[R := R] \as Types;
  \structure Family := {
    Carrier: R -> \Set,
    maps: \forall (n: R) -> Types.Maps (Carrier n),
  };
  \structure FamilyGroup := { family: Family };
  \module Consume(family: Family) {
    \definition Data: \Set := \forall (n: R) -> family.Carrier n;
  }
}
\module Readers(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \module Of(P: Families.FamilyGroup) {
    \definition Data: \Set := \forall (n: R) -> P.family.Carrier n;
  }
  \module Packing {
    \import \root.Readers[R := R] \as Readers;
    \definition makeFamily[P: Families.FamilyGroup]: Families.Family := Families.Family {
      Carrier := P.family.Carrier, maps := P.family.maps,
    };
    \structure PackedFamily := {
      group: Families.FamilyGroup,
      data: Readers.Of[P := group].Data,
    };
    \definition make[P: Families.FamilyGroup][p: Readers.Of[P := P].Data]: PackedFamily :=
      PackedFamily { group := P, data := p };
  }
}
\module Use(R: \Set) {
  \import \root.Families[R := R] \as Families;
  \import \root.Readers[R := R].Packing[] \as Packing;
  \module Of(P: Families.FamilyGroup, p: \root.Readers[R := R].Of[P := P].Data) {
    \definition sequence: Packing.PackedFamily := Packing.make P p;
    \import Families.Consume[family := Packing.makeFamily P] \as Consumed;
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
