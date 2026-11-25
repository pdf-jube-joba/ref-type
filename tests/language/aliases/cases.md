# aliases / cases

## body type

The alias body does not have its declared type.

```toml case
id = "reject-aliases.body_type"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\definition Wrong[A: \Set]: \Set := A -> \Prop;
```

## dependent argument type

A later alias argument does not have the type determined by an earlier argument.

```toml case
id = "reject-aliases.dependent_argument_type"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Other: \Set := | other: Other;
\definition Identity[A: \Set, x: A]: A := x;
\definition bad: Unit := Identity[Unit, Other::other];
```

## parameter count

The alias lacks arguments, and the remaining higher sort cannot be used as a term's type.

```toml case
id = "reject-aliases.parameter_count"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\definition Relation[A: \Set]: \PropKind := A -> A -> \Prop;
\definition bad: \PropKind := Relation;
```

## unused argument type

An alias argument unused in the body also has a type mismatch.

```toml case
id = "reject-aliases.unused_argument_type"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\definition Ignore[A: \Set]: \Prop := \forall (P: \Prop) -> P -> P;
\definition bad: \Prop := Ignore[Unit::unit];
```

## aliases

Substituting arguments into the alias body yields the declared type.

```toml case
id = "accept-aliases"
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


## expected types reach grouped dependent local and record bodies

The outer expected type propagates into grouped binders, dependent result types, lets, and record bodies.

```toml case
id = "expected_types_reach_grouped_dependent_local_and_record_bodies"
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

## chained and instantiated aliases keep parameters and reduce

Repeated specialization through inductive-type aliases preserves matching constructor and induction arguments and supports reduction.

```toml case
id = "chained_and_instantiated_aliases_keep_parameters_and_reduce"
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

## indexed alias induction preserves its motive telescope

Induction returning the same index can be defined for an alias of an indexed inductive type.

```toml case
id = "indexed_alias_induction_preserves_its_motive_telescope"
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

## take accepts a codomain independent after reduction

After reduction, the result type does not depend on the witness, so a proof can be returned after existential elimination.

```toml case
id = "take_accepts_a_codomain_independent_after_reduction"
scope = "module"
expect = "accept"
name = "Example"
parameters = '''A: \Set, y: A'''
```

```ref
\definition proof: (\exists A) -> y = y :=
  \fun (exists: \exists A) => \block {
  \takefrom x: A \by exists \then
  \return \refl((\fun (z: A) => y) x)
};
```

## Alias type checking / 1

A value of the wrong type is passed to a constructor field; it is rejected even through an alias.

```toml case
id = "alias-check-0"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias := Alias::cons Unit::unit Alias::nil;
```

## Alias type checking / 2

The specified associated item does not exist; it is rejected even through an alias.

```toml case
id = "alias-check-1"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias := Alias::missing;
```

## Alias type checking / 3

Induction branches are missing; it is rejected even through an alias.

```toml case
id = "alias-check-2"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias -> Alias :=
  \induction (xs: Alias) \return Alias \with { | nil: Alias::nil };
```

## Alias type checking / 4

Branches for the same constructor are duplicated; it is rejected even through an alias.

```toml case
id = "alias-check-3"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias -> Alias :=
  \induction (xs: Alias) \return Alias \with {
  | nil: Alias::nil | nil: Alias::nil
};
```

## Alias type checking / 5

The induction result type differs from the branch term's type; it is rejected even through an alias.

```toml case
id = "alias-check-4"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias -> Unit :=
  \induction (xs: Alias) \return Unit \with {
  | nil: Alias::nil
  | cons: \fun (x: Bit) (xs: Alias) (ih: Unit) => ih
};
```

## Alias type checking / 6

A subset is not itself an inductive type; it is rejected even through an alias.

```toml case
id = "alias-check-5"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition Refined: \Set := \Cast[Alias] ({ xs: Alias \where xs = xs });
\definition bad: Refined := Refined::nil;
```

## Alias type checking / 7

A function type is not inductive; it is rejected even through an alias.

```toml case
id = "alias-check-6"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition Function: \Set := Unit -> Unit;
\definition bad: Function := Function::unit;
```

## Alias type checking / 8

A value of a different inductive type is passed as an alias type argument; it is rejected even through an alias.

```toml case
id = "alias-check-7"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition Discard[x: Unit]: \Set := List[Bit];
\definition bad: Alias := Discard[Bit::zero]::nil;
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
