# system / equality

## equality rejects proofs

集合の要素を比較する等号で証明項を比較しているため、拒否される。

```toml case
id = "reject-system.equality_rejects_proofs"
scope = "module"
expect = "reject"
name = "EqualityRejectsProofs"
parameters = '''P: \Prop,
    p: P,'''
```

```ref
\definition bad: \Prop := p = p;
```

## equality requires common set

等号の両辺が共通の集合の要素になっていないため、拒否される。

```toml case
id = "reject-system.equality_requires_common_set"
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

## funext wrong pointwise

関数外延性に渡した証明が指定された二つの関数の各点等式ではないため、拒否される。

```toml case
id = "reject-system.funext_wrong_pointwise"
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

## id elim wrong base

等号除去の基底証明が motive の反射の場合を示していないため、拒否される。

```toml case
id = "reject-system.id_elim_wrong_base"
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

## setext wrong inclusion

集合外延性の包含証明が指定された二つの集合を結ばないため、拒否される。

```toml case
id = "reject-system.setext_wrong_inclusion"
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

## equality transport

等号に沿って型と証明を移送できるため、受理される。

```toml case
id = "accept-system.equality_transport"
scope = "module"
expect = "accept"
name = "Transport"
parameters = '''A: \Set, F: A -> \Set, a, b: A'''
```

```ref
\definition cast(value: F a)(same: a = b): F b :=
  \idelim a = b \with x: _ => F x \by { base: value, equality: same };
\definition selfCast(value: F a)(same: a = a): F a :=
  \idelim a = a \with x: _ => F x \by { base: value, equality: same };
\definition identity: \forall (value: F a)(same: a = a) -> selfCast value same = value :=
  \fun (value: F a)(same: a = a) =>
    \transporteq a \with x: _ => F x \by { base: value };
```


## transport specialization and macro binders

Set(1) の family に対する transport の等式を、macro と module の特殊化を経ても利用できる。

```toml case
id = "transport_specialization_and_macro_binders"
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

## neutral transport supports subsets functions projections and induction

仮定した等式による transport の結果を、関数適用、field の射影、induction と subset の値として利用できる。

```toml case
id = "neutral_transport_supports_subsets_functions_projections_and_induction"
scope = "module"
expect = "accept"
name = "T"
parameters = '''A: \Set, a, b: A'''
```

```ref
\inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
\structure Pair: \Set { first: Nat, second: Nat }
\definition moveNat(value: Nat)(same: a = b): Nat :=
  \idelim a = b \with x: _ => Nat \by { base: value, equality: same };
\definition count: Nat -> Nat := \induction (n: Nat) \return Nat \with {
  | zero: Nat::zero | succ: \fun (n, previous: Nat) => Nat::succ previous
};
\definition countMoved(value: Nat)(same: a = b): Nat := count (moveNat value same);
\definition apply(f: Nat -> Nat)(same: a = b): Nat :=
  (\idelim a = b \with x: _ => Nat -> Nat \by { base: f, equality: same }) Nat::zero;
\definition project(p: Pair)(same: a = b): Nat :=
  (\idelim a = b \with x: _ => Pair \by { base: p, equality: same }) #first;
\definition Sub: \Set := \Cast[Nat] ({ n: Nat \where n = n });
\definition subset(value: Sub)(same: a = b): Sub :=
  \idelim a = b \with x: _ => Sub \by { base: value, equality: same };
\definition law: \forall (value: Sub) ->
  (\idelim a = a \with x: _ => Sub \by { base: value, equality: \refl a }) = value :=
  \fun (value: _) => \transporteq a \with x: _ => Sub \by { base: value };
```

## transport substitutes through nested family binders

family 内の binder を保ちながら、外側の等式に従って型を移し替えられる。

```toml case
id = "transport_substitutes_through_nested_family_binders"
scope = "module"
expect = "accept"
name = "T"
parameters = '''A: \Set(1), F: A -> A -> \Set, a, b: A'''
```

```ref
\definition cast(value: \forall (y: A) -> F a y)(same: a = b): \forall (y: A) -> F b y :=
  \idelim a = b \with x: _ => \forall (y: A) -> F x y \by { base: value, equality: same };
\definition identity: \forall (value: \forall (y: A) -> F a y) ->
  (\idelim a = a \with x: _ => \forall (y: A) -> F x y \by { base: value, equality: \refl a }) = value :=
  \fun (value: _) => \transporteq a \with x: _ => \forall (y: A) -> F x y \by { base: value };
```

## transport checks base and equality certificates

移し替える前の型に合わない base を渡すため拒否される。

```toml case
id = "transport_checks_base_and_equality_certificates"
scope = "module"
expect = "reject"
name = "T"
parameters = '''A: \Set, F: A -> \Set, a, b: A, v: F b, e: a = b'''
```

```ref
\definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: e };
```

## transport checks base and equality certificates 1

移し替えの向きと等式の証明の向きが逆なので拒否される。

```toml case
id = "transport_checks_base_and_equality_certificates-1"
scope = "module"
expect = "reject"
name = "T"
parameters = '''A: \Set, F: A -> \Set, a, b: A, v: F a, e: b = a'''
```

```ref
\definition bad: F b := \idelim a = b \with x: _ => F x \by { base: v, equality: e };
```

## transport substitutes through nested family binders 1

transporteq の family に命題を指定しているため拒否される。

```toml case
id = "transport_substitutes_through_nested_family_binders-1"
scope = "module"
expect = "reject"
name = "T"
parameters = '''A: \Set, a: A, P: A -> \Prop, p: P a'''
```

```ref
\infer \transporteq a \with x: _ => P x \by { base: p };
```
