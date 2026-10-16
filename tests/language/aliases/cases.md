# aliases / cases

## body type

alias の本体が宣言された型を持たない。

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

後続の alias 引数が先行する引数から決まる型を持たない。

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

alias の引数が不足しており、残った上位 sort を項の型として使えない。

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

本体で使わない alias 引数にも型の不一致がある。

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

alias の本体を引数で置換すると宣言された型を持つ。

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

  \definition reflexive(A: \Set)(r: Relation[A]): \Prop :=
    \forall (x: A) -> r x x;
  \definition atSelf(A: \Set)(x: A): At[_, x, \fun (y: A) => x = y] :=
    \refl(x);
  \definition identity(A: \Set)(x: A): Identity[A, x] = x := \refl(x);
  \definition capture(A: \Set)(x, y: A): Constant[A, x, y] y = x := \refl(x);
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
  \definition relation(B: \Set)(r: L.Relation[B])(y: B): \Prop := r x y;
}

\module AliasUse {
  \inductive Unit: \Set := | unit: Unit;
  \import \root.AliasClient[A := Unit, x := Unit::unit] \as C;
  \definition self: C.Equal[Unit::unit] := C.self;
}
```


## expected types reach grouped dependent local and record bodies

外側の期待型を、まとめた binder、依存する結果型、let、record の body に伝えられる。

```toml case
id = "expected_types_reach_grouped_dependent_local_and_record_bodies"
scope = "module"
expect = "accept"
name = "Expected"
parameters = '''A: \Set, P: A -> \Prop'''
```

```ref
\structure Pair: \Set { first: A, second: A }
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
\structure Maps: \Set { get: Pair -> A }
\definition maps: Maps := Maps { get := \block {
    \fun (p: _) \then \return p.second
  } };
\definition Sub: \Set := \Cast[A] ({ x: A \where P x });
\definition property: \forall (x: Sub) -> P x :=
  \fun (x: _) => \bysub(A, Sub, x);
```

## chained and instantiated aliases keep parameters and reduce

帰納型の alias を重ねて特殊化しても、constructor と induction の引数が対応して簡約できる。

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
  \definition Generic(B: \Set): \Set := List[B];
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

index を取る帰納型の alias に対して、同じ index を返す induction を定義できる。

```toml case
id = "indexed_alias_induction_preserves_its_motive_telescope"
scope = "module"
expect = "accept"
name = "Indexed"
parameters = '''A: \Set'''
```

```ref
\inductive Family[B: \Set]: \forall (x: B) -> \Set := | intro: \forall (x: B) -> Family x;
\definition Alias(x: A): \Set := Family[A] x;
\definition copy: \forall (x: A) -> Alias x -> Alias x :=
  \induction (x: A) (value: Alias x) \return Alias x \with {
  | intro: \fun (x: A) => Family[A]::intro x
};
\definition law(x: A): copy x (Family[A]::intro x) = Family[A]::intro x :=
  \refl(Family[A]::intro x);
```

## take accepts a codomain independent after reduction

結果型は簡約後には witness に依存しないため、exists の除去後にも証明を返せる。

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

## alias の型検査 / 1

constructor の field に違う型の値を渡している。alias を経ても拒否される。

```toml case
id = "alias-check-0"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias := Alias::cons Unit::unit Alias::nil;
```

## alias の型検査 / 2

指定した associated item が存在しない。alias を経ても拒否される。

```toml case
id = "alias-check-1"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition bad: Alias := Alias::missing;
```

## alias の型検査 / 3

induction の branch が不足している。alias を経ても拒否される。

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

## alias の型検査 / 4

同じ constructor の branch を重複している。alias を経ても拒否される。

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

## alias の型検査 / 5

induction の結果の型と branch の項の型が異なる。alias を経ても拒否される。

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

## alias の型検査 / 6

subset は帰納型そのものではない。alias を経ても拒否される。

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

## alias の型検査 / 7

関数型は帰納型ではない。alias を経ても拒否される。

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

## alias の型検査 / 8

alias の型引数に違う帰納型の値を渡している。alias を経ても拒否される。

```toml case
id = "alias-check-7"
scope = "module"
expect = "reject"
name = "Negative"
```

```ref
\inductive Unit: \Set := | unit: Unit; \inductive Bit: \Set := | zero: Bit | one: Bit; \inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List; \definition Alias: \Set := List[Bit]; \definition Discard(x: Unit): \Set := List[Bit];
\definition bad: Alias := Discard[Bit::zero]::nil;
```

## 命題の alias からの大きな除去

複数の constructor を持つ命題を消去して sort を返している。

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
