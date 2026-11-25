# Equality and transport

## Equality rejects proofs

Proof terms are compared with equality intended for set elements.

```toml case
id = "equality-rejects-proofs"
scope = "module"
expect = "reject"
name = "EqualityRejectsProofs"
parameters = '''P: \Prop,
    p: P,'''
```

```ref
\definition bad: \Prop := p = p;
```

## Equality requires common set

The equality's two sides are not elements of a common set.

```toml case
id = "equality-requires-common-set"
scope = "module"
expect = "reject"
name = "EqualityRequiresCommonSet"
parameters = '''A, B: \Set(0),
    a: A,
    b: B,'''
```

```ref
\definition bad: \Prop := a = b;
```

## Funext wrong pointwise

The proof passed to function extensionality does not establish pointwise equality of the specified functions.

```toml case
id = "funext-wrong-pointwise"
scope = "module"
expect = "reject"
name = "FunExtWrongPointwise"
parameters = '''X, Y: \Set,
    f, g: X -> Y,
    P: \Prop,
    wrong: \forall (x: X) -> P,'''
```

```ref
\definition bad: f = g := \axiom:funext(f, g, wrong);
```

## Id elim wrong base

The base proof for equality elimination does not establish the motive's reflexive case.

```toml case
id = "id-elim-wrong-base"
scope = "module"
expect = "reject"
name = "IdentityElimWrongBase"
parameters = '''A: \Set(0),
    P: A -> \Prop,
    Q: \Prop,
    a, b: A,
    ab: a = b,
    q: Q,'''
```

```ref
\definition bad: P b :=
    \idelim a = b \with x: A => P x \by { base: q, equality: ab };
```

## Setext wrong inclusion

The inclusion proofs for set extensionality do not relate the specified sets.

```toml case
id = "setext-wrong-inclusion"
scope = "module"
expect = "reject"
name = "SetExtWrongInclusion"
parameters = '''X: \Set,
    A, B: \Pow (X),
    aa: \forall (x: X) -> \In[X] (A) (x) -> \In[X] (A) (x),
    ba: \forall (x: X) -> \In[X] (B) (x) -> \In[X] (A) (x),'''
```

```ref
\definition bad: A = B := \axiom:setext(A, B, aa, ba);
```

## Equality transport

Types and proofs can be transported along equality.

```toml case
id = "equality-transport"
scope = "module"
expect = "accept"
name = "Transport"
parameters = '''A: \Set, F: A -> \Set, a, b: A'''
```

```ref
\definition cast[value: F a][same: a = b]: F b :=
  \idelim a = b \with x: _ => F x \by { base: value, equality: same };
\definition selfCast[value: F a][same: a = a]: F a :=
  \idelim a = a \with x: _ => F x \by { base: value, equality: same };
\definition identity: \forall (value: F a)(same: a = a) -> selfCast value same = value :=
  \fun (value: F a)(same: a = a) =>
    \transporteq a \with x: _ => F x \by { base: value };
```


## Transport families resolve record fields

Equality transport and its reflexivity-law family can reference fields of bound records.

```toml case
id = "transport-families-resolve-record-fields"
scope = "module"
expect = "accept"
```

```ref
\inductive Bit: \Set := | zero: Bit | one: Bit;
\structure Entry: \Set := { value: Bit, same: value = value };
\structure Marker: \Set := { marker: Bit };
\definition projected[a, b: Entry][same: a = b]: a.value = b.value :=
  \idelim a = b \with entry: Entry => a.value = entry.value
    \by { base: \refl(a.value), equality: same };
\definition inferred[a, b: Entry][same: a = b]: a.value = b.value :=
  \idelim a = b \with entry: _ => a.value = entry.value
    \by { base: \refl(a.value), equality: same };
\definition shadow[a, b: Entry][entry: Marker][same: a = b]: a.value = b.value :=
  \idelim a = b \with entry: Entry => a.value = entry.value
    \by { base: (\fun (marker: Bit) => \refl(a.value)) entry.marker, equality: same };
\module Read(entry: Entry) {
  \definition value: Bit := entry.value;
}
\definition instantiated[a, b: Entry][same: a = b]: a.value = b.value :=
  \idelim a = b \with entry: Entry => a.value = Read[entry := entry].value
    \by { base: \refl(a.value), equality: same };
\definition Family[entry: Entry]: \Set := \Cast[Bit] ({ x: Bit \where x = entry.value });
\definition cast[a, b: Entry][value: Family a][same: a = b]: Family b :=
  \idelim a = b \with entry: Entry => \Cast[Bit] ({ x: Bit \where x = entry.value })
    \by { base: value, equality: same };
\definition identity[a: Entry][value: Family a]:
  (\idelim a = a \with entry: _ => \Cast[Bit] ({ x: Bit \where x = entry.value })
    \by { base: value, equality: \refl(a) }) = value :=
  \transporteq a \with entry: _ => \Cast[Bit] ({ x: Bit \where x = entry.value })
    \by { base: value };
```

## Transport specialization and macro binders

Transport equalities for Set(1) families remain usable through macros and module specialization.

```toml case
id = "transport-specialization-and-macro-binders"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module T(A: \Set, a: A, F: A -> \Set(1)) {
  \macro move($v) := \idelim a = a \with x: _ => F x \by { base: $v, equality: \refl a };
  \definition law: \forall (value: F a) -> move!{value} = value :=
    \fun (value: _) => \transporteq a \with x: _ => F x \by { base: value };
}
\module U(A: \Set, a: A, F: A -> \Set(1)) {
  \import \root.T[A := A, a := a, F := F] \as T;
  \definition law: \forall (value: F a) ->
    (\idelim a = a \with x: _ => F x \by { base: value, equality: \refl a }) = value := T.law;
}
```

## Neutral transport in elimination contexts

Transport along an assumed equality can be used in function application, field projection, induction, and as a subset value.

```toml case
id = "neutral-transport-in-elimination-contexts"
scope = "module"
expect = "accept"
parameters = '''A: \Set, a, b: A'''
```

```ref
\inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
\structure Pair: \Set := { first: Nat, second: Nat };
\definition moveNat[value: Nat][same: a = b]: Nat :=
  \idelim a = b \with x: _ => Nat \by { base: value, equality: same };
\definition count: Nat -> Nat := \induction (n: Nat) \return Nat \with {
  | zero: Nat::zero | succ: \fun (n, previous: Nat) => Nat::succ previous
};
\definition countMoved[value: Nat][same: a = b]: Nat := count (moveNat value same);
\definition apply[f: Nat -> Nat][same: a = b]: Nat :=
  (\idelim a = b \with x: _ => Nat -> Nat \by { base: f, equality: same }) Nat::zero;
\definition project[p: Pair][same: a = b]: Nat :=
  (\idelim a = b \with x: _ => Pair \by { base: p, equality: same }).first;
\definition Sub: \Set := \Cast[Nat] ({ n: Nat \where n = n });
\definition subset[value: Sub][same: a = b]: Sub :=
  \idelim a = b \with x: _ => Sub \by { base: value, equality: same };
\definition law: \forall (value: Sub) ->
  (\idelim a = a \with x: _ => Sub \by { base: value, equality: \refl a }) = value :=
  \fun (value: _) => \transporteq a \with x: _ => Sub \by { base: value };
```

## Transport substitutes through nested family binders

Types can be transported along an outer equality while preserving binders within the family.

```toml case
id = "transport-substitutes-through-nested-family-binders"
scope = "module"
expect = "accept"
parameters = '''A: \Set(1), F: A -> A -> \Set, a, b: A'''
```

```ref
\definition cast[value: \forall (y: A) -> F a y][same: a = b]: \forall (y: A) -> F b y :=
  \idelim a = b \with x: _ => \forall (y: A) -> F x y \by { base: value, equality: same };
\definition identity: \forall (value: \forall (y: A) -> F a y) ->
  (\idelim a = a \with x: _ => \forall (y: A) -> F x y \by { base: value, equality: \refl a }) = value :=
  \fun (value: _) => \transporteq a \with x: _ => \forall (y: A) -> F x y \by { base: value };
```

## Transport checks the base term type

The supplied base does not match the type before transport.

```toml case
id = "transport-base-type-mismatch"
scope = "module"
expect = "reject"
parameters = '''A: \Set, F: A -> \Set, a, b: A, v: F b, e: a = b'''
```

```ref
\definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: e };
```

## Transport checks the equality proof direction

The transport direction is opposite to the equality proof's direction.

```toml case
id = "transport-equality-direction-mismatch"
scope = "module"
expect = "reject"
parameters = '''A: \Set, F: A -> \Set, a, b: A, v: F a, e: b = a'''
```

```ref
\definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: e };
```

## Transport identity requires a set-valued family

A proposition is specified as the family for transporteq.

```toml case
id = "transport-identity-requires-set-family"
scope = "module"
expect = "reject"
parameters = '''A: \Set, a: A, P: A -> \Prop, p: P a'''
```

```ref
\infer \transporteq a \with x: _ => P x \by { base: p };
```
