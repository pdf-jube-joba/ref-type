# Existential elimination and proof terms

## Exists intro wrong witness

The existential witness is not an element of the specified set.

```toml case
id = "exists-intro-wrong-witness"
scope = "module"
expect = "reject"
name = "ExistsIntroWrongWitness"
parameters = '''A, B: \Set(0),
    b: B,'''
```

```ref
\definition bad: \exists A := \exact(b, A);
```

## Exists requires set

The subject of existential quantification is not a set.

```toml case
id = "exists-requires-set"
scope = "module"
expect = "reject"
name = "ExistsRequiresSet"
parameters = '''P: \Prop,'''
```

```ref
\definition bad: \Prop := \exists P;
```

## Take prop wrong existence

The existence proof for take does not concern the required proposition.

```toml case
id = "take-prop-wrong-existence"
scope = "module"
expect = "reject"
name = "TakePropWrongExistence"
parameters = '''X, Y: \Set(0),
    P: \Prop,
    predicate: X -> P,
    existsY: \exists Y,'''
```

```ref
\definition bad: P :=
    \take (x: X) => predicate x \by { existsY };
```

## Set runs require a termination proof

The supplied certificate is a state value rather than a proof that the Set run terminates.

```toml case
id = "set-run-requires-termination-proof"
scope = "module"
expect = "reject"
name = "WrongRunProof"
parameters = '''A: \Set,
  B: \Set,
  step: A -> \RunStep[A, B],
  initial: A'''
```

```ref
\definition bad: B := \run[A, B](step, initial) \by { initial };
```

## Local take

An existential witness can be used locally to prove the conclusion.

```toml case
id = "local-take"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
/* Set and proof binders remain in scope beneath choice and take. */
\module LocalTake(X: \Set, existsX: \exists X) {
    \definition local_prop: \forall (p: \Prop) -> p -> p :=
        \fun (p: \Prop) (hp: p) => \take (x: X) => hp \by { existsX };
    \definition Singleton [T: \Set] [t: T]: \Set :=
        \Cast[T] ({ x : T \where x = t });
    \definition witness [T: \Set] [t: T]: Singleton T t :=
        \into[T](t, { x : T \where x = t }) \by { \refl t };
    \definition unique [T: \Set] [t: T] [a, b: Singleton T t]: a = b :=
        \idelim t = b \with x: T => a = x
          \by { base: \bysub(T, { x : T \where x = t }, a),
            equality: \idelim b = t \with x: T => x = b
              \by { base: \refl b, equality: \bysub(T, { x : T \where x = t }, b) } };
    \definition local_set [T: \Set] [t: T]: T :=
        \choice Singleton T t
          \by { existence: \exact(witness T t, Singleton T t), uniqueness: unique T t };
    \definition local_equality [T: \Set] [t: T]: t = local_set T t :=
        \choiceeq witness T t \of Singleton T t
          \by { existence: \exact(witness T t, Singleton T t), uniqueness: unique T t };
}

\module NormalizedTake(X: \Set, existsX: \exists X) {
    \definition through_local_binding: \forall (p: \Prop) -> p -> p := \block {
        \fun (p: \Prop) (proof: p) \then
        \takefrom x: X \by existsX \then
        \let result: p := proof \then
        \return result
    };
}
```

## Nested proofs

Proof terms can be used inside applications and subset introductions.

```toml case
id = "nested-proofs"
scope = "module"
expect = "accept"
name = "NestedProofs"
parameters = '''A: \Set(0),
    P: A -> \Prop,
    a, b, c: A,
    pa: P a,
    ab: a = b,
    bc: b = c,
    consume: \forall (x: A) -> P x -> P x,'''
```

```ref
\definition pb: P b :=
    \idelim a = b \with x: A => P x \by { base: pa, equality: ab };
\definition pc: P c :=
    \idelim b = c \with x: A => P x \by { base: pb, equality: bc };

/* App checks an IdElim result as a dependent proof argument. */
\definition consume_transported: P b :=
    consume b (\idelim a = b \with x: A => P x \by { base: pa, equality: ab });
\definition consume_twice_transported: P c :=
    consume c
        (\idelim b = c \with x: A => P x
         \by { base: \idelim a = b \with x: A => P x \by { base: pa, equality: ab }, equality: bc });

\definition PSet: \Pow (A) := { x : A \where P x };
\definition PA: \Set(0) := \Cast[A] (PSet);
/* SubsetIntro checks an IdElim tree as its membership certificate. */
\definition refined_b: PA :=
    \into[A](b, PSet) \by { \idelim a = b \with x: A => P x \by { base: pa, equality: ab } };
\definition refined_c: PA :=
    \into[A](c, PSet) \by { \idelim b = c \with x: A => P x \by { base: pb, equality: bc } };

\definition nested_exists: \exists A :=
    \exact((\fun (f: A -> A) => f b) (\fun (x: A) => x), A);
```

## Contextual reflexivity proofs

A contextual definition can prove that its element argument equals itself.

```toml case
id = "contextual-reflexivity-proof"
scope = "module"
expect = "accept"
name = "Reflexivity"
parameters = '''A: \Set'''
```

```ref
\definition reflexive[x: A]: x = x :=
  \refl(x);
```

