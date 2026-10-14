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

