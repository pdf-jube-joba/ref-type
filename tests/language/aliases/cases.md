# Type aliases

## Body type

The alias body does not have its declared type.

```toml case
id = "body-type"
scope = "module"
expect = "reject"
```

```ref
\definition Wrong[A: \Set]: \Set := A -> \Prop;
```

## Dependent argument type

A later alias argument does not have the type determined by an earlier argument.

```toml case
id = "dependent-argument-type"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Other: \Set := | other: Other;
\definition Identity[A: \Set, x: A]: A := x;
\definition bad: Unit := Identity[Unit, Other::other];
```

## Parameter count

The alias lacks arguments, and the remaining higher sort cannot be used as a term's type.

```toml case
id = "parameter-count"
scope = "module"
expect = "reject"
```

```ref
\definition Relation[A: \Set]: \PropKind := A -> A -> \Prop;
\definition bad: \PropKind := Relation;
```

## Unused argument type

An alias argument unused in the body also has a type mismatch.

```toml case
id = "unused-argument-type"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\definition Ignore[A: \Set]: \Prop := \forall (P: \Prop) -> P -> P;
\definition bad: \Prop := Ignore[Unit::unit];
```

## Alias substitution through local and imported definitions

Substituting arguments into the alias body yields the declared type.

```toml case
id = "alias-substitution-and-imports"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Aliases {
  \inductive Unit: \Set := | unit: Unit;
  \definition Relation[Carrier: \Set]: \PropKind := Carrier -> Carrier -> \Prop;
  \definition Predicate[A: \Set]: _ := A -> \Prop;
  \definition At[A: \Set, x: A, P: Predicate[A]]: \Prop := P x;
  \definition Identity[A: \Set, x: A]: A := x;
  \definition Truth: \Prop := \forall (P: \Prop) -> P -> P;
  \definition Constant[A: \Set, x, y: A]: _ := \fun (z: A) => x;

  \definition reflexive[A: \Set][r: Relation[A]]: \Prop :=
    \forall (x: A) -> r x x;
  \definition atSelf[A: \Set][x: A]: At[_, x, \fun (y: A) => x = y] :=
    \refl(x);
  \definition identity[A: \Set][x: A]: Identity[A, x] = x := \refl(x);
  \definition capture[A: \Set][x, y: A]: Constant[A, x, y] y = x := \refl(x);
  \definition truth: Truth[] := \fun (P: \Prop) => \fun (p: P) => p;
  \check Relation[Unit]: \PropKind;
}

\module AliasLibrary(A: \Set, x: A) {
  \definition Equal[y: A]: \Prop := x = y;
  \definition Relation[B: \Set]: \PropKind := A -> B -> \Prop;
  \definition Applied[B: \Set, y: B, r: Relation[B]]: \Prop := r x y;
  \inductive Unit: \Set := | unit: Unit;
  \definition Element: \Set := Unit;
  \definition Value: Element := Unit::unit;
}

\module AliasClient(A: \Set, x: A) {
  \import \root.AliasLibrary[A := A, x := x] \as L;
  \definition Equal[y: A]: _ := L.Equal[y];
  \definition self: Equal[x] := \refl(x);
  \definition applied: L.Applied[A, x, \fun (a, b: A) => a = b] := \refl(x);
  \definition value: L.Element := L.Value;
  \definition nominal: value = L.Unit::unit := \refl(value);
  \definition relation[B: \Set][r: L.Relation[B]][y: B]: \Prop := r x y;
}

\module AliasUse {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.AliasClient[A := Unit, x := Unit::unit] \as C;
  \definition self: C.Equal[Unit::unit] := C.self;
}
```


## Expected types reach grouped dependent local and record bodies

The outer expected type propagates into grouped binders, dependent result types, lets, and record bodies.

```toml case
id = "expected-types-reach-grouped-dependent-local-and-record-bodies"
scope = "module"
expect = "accept"
name = "Expected"
parameters = '''A: \Set, P: A -> \Prop'''
```

```ref
\structure Pair: \Set := { first: A, second: A };
\definition first: Pair -> A := \block {
  \fun (pair: _) \then
  \let project: Pair -> A := \fun (p: _) => p.first \then
  \return project pair
};
\definition grouped: Pair -> Pair -> A :=
  \fun (left, right: _) => left.first;
\definition dependent: \forall (p: Pair) -> p.first = p.first :=
  \fun (p: _) => \refl(p.first);
\definition nested: \forall (X: \Set) -> X -> X -> X :=
  \fun (X: _) (x, y: _) => x;
\definition ascribed: Pair -> A :=
  (\fun (p: _) => p.first) \of Pair -> A;
\structure Maps: \Set := { get: Pair -> A };
\definition maps: Maps := Maps { get := \block {
    \fun (p: _) \then \return p.second
  } };
\definition Sub: \Set := \Cast[A] ({ x: A \where P x });
\definition property: \forall (x: Sub) -> P x :=
  \fun (x: _) => \bysub(A, Sub, x);
```

## Chained and instantiated aliases keep parameters and reduce

Repeated specialization through inductive-type aliases preserves matching constructor and induction arguments and supports reduction.

```toml case
id = "chained-and-instantiated-aliases-keep-parameters-and-reduce"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Lists(A: \Set) {
  \inductive List[B: \Set]: \Set := | nil: List | cons: B -> List -> List;
  \definition Values: \Set := List[A];
  \definition Alias: \Set := Values;
  \definition Generic[B: \Set]: \Set := List[B];
  \definition empty: Values := Alias::nil;
  \definition generic: Values := Generic[A]::nil;
  \definition copy: Alias -> Alias :=
    \induction (xs: Alias) \return Alias \with {
    | cons: \fun (x: A) (xs, previous: Alias) => Alias::cons x previous
    | nil: Alias::nil
  };
  \definition onNil: copy empty = empty := \refl(empty);
}
\module Use {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.Lists[A := Unit] \as L;
  \definition Values: \Set := L.Alias;
  \definition singleton: Values := Values::cons Unit::unit Values::nil;
  \definition onCons: L.copy singleton = singleton := \refl(singleton);
}
```

## Indexed alias induction preserves its motive telescope

Induction returning the same index can be defined for an alias of an indexed inductive type.

```toml case
id = "indexed-alias-induction-preserves-its-motive-telescope"
scope = "module"
expect = "accept"
name = "Indexed"
parameters = '''A: \Set'''
```

```ref
\inductive Family[B: \Set]: \forall (x: B) -> \Set := | intro: \forall (x: B) -> Family x;
\definition Alias[x: A]: \Set := Family[A] x;
\definition copy: \forall (x: A) -> Alias x -> Alias x :=
  \induction (x: A) (value: Alias x) \return Alias x \with {
  | intro: \fun (x: A) => Family[A]::intro x
};
\definition law[x: A]: copy x (Family[A]::intro x) = Family[A]::intro x :=
  \refl(Family[A]::intro x);
```

## Take accepts a codomain independent after reduction

After reduction, the result type does not depend on the witness, so a proof can be returned after existential elimination.

```toml case
id = "take-accepts-a-codomain-independent-after-reduction"
scope = "module"
expect = "accept"
parameters = '''A: \Set, y: A'''
```

```ref
\definition proof: (\exists A) -> y = y :=
  \fun (exists: \exists A) => \block {
  \takefrom x: A \by exists \then
  \return \refl((\fun (z: A) => y) x)
};
```

## Constructor field types through aliases

A value of the wrong type is passed to a constructor field; it is rejected even through an alias.

```toml case
id = "alias-constructor-field-type-mismatch"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition bad: Bits := Bits::cons Unit::unit Bits::nil;
```

## Unknown associated items through aliases

The specified associated item does not exist; it is rejected even through an alias.

```toml case
id = "alias-unknown-associated-item"
scope = "module"
expect = "reject"
```

```ref
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition bad: Bits := Bits::missing;
```

## Missing induction branches through aliases

Induction branches are missing; it is rejected even through an alias.

```toml case
id = "alias-induction-missing-branch"
scope = "module"
expect = "reject"
```

```ref
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition bad: Bits -> Bits :=
  \induction (xs: Bits) \return Bits \with {
    | nil: Bits::nil
  };
```

## Duplicate induction branches through aliases

Branches for the same constructor are duplicated; it is rejected even through an alias.

```toml case
id = "alias-induction-duplicate-branch"
scope = "module"
expect = "reject"
```

```ref
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition bad: Bits -> Bits :=
  \induction (xs: Bits) \return Bits \with {
    | nil: Bits::nil
    | nil: Bits::nil
  };
```

## Induction result types through aliases

The induction result type differs from the branch term's type; it is rejected even through an alias.

```toml case
id = "alias-induction-wrong-result-type"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition bad: Bits -> Unit :=
  \induction (xs: Bits) \return Unit \with {
    | nil: Bits::nil
    | cons: \fun (x: Bit) (xs: Bits) (previous: Unit) => previous
  };
```

## Refinement aliases do not expose carrier constructors

A subset is not itself an inductive type; it is rejected even through an alias.

```toml case
id = "refinement-alias-is-not-inductive"
scope = "module"
expect = "reject"
```

```ref
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition Refined: \Set := \Cast[Bits] ({ xs: Bits \where xs = xs });
\definition bad: Refined := Refined::nil;
```

## Function aliases do not expose constructors

A function type is not inductive; it is rejected even through an alias.

```toml case
id = "function-alias-is-not-inductive"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\definition Endomorphism: \Set := Unit -> Unit;
\definition bad: Endomorphism := Endomorphism::unit;
```

## Unused alias arguments are still checked

A value of a different inductive type is passed as an alias type argument; it is rejected even through an alias.

```toml case
id = "alias-unused-argument-type-mismatch"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Bit: \Set := | zero: Bit | one: Bit;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition Bits: \Set := List[Bit];
\definition Ignore[x: Unit]: \Set := List[Bit];
\definition bad: Bits := Ignore[Bit::zero]::nil;
```

## Large elimination from a proposition alias

A proposition with multiple constructors is eliminated to return a sort.

```toml case
id = "alias-large-elimination"
scope = "module"
expect = "reject"
name = "LargeElimination"
```

```ref
\inductive Either: \Prop := | left: Either | right: Either;
\definition Alias: \Prop := Either;
\definition bad: Alias -> \Prop :=
  \induction (p: Alias) \return \Prop \with { | left: Either | right: Either };
```
