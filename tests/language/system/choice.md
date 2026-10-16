# system / choice

## choice eq wrong element

choice の等式証明に渡した要素が指定された集合に属さない。

```toml case
id = "reject-system.choice_eq_wrong_element"
scope = "module"
expect = "reject"
name = "WrongElement"
parameters = '''A, B: \Set, a: A, b: B, unique: \forall (x, y: A) -> x = y'''
```

```ref
\definition bad: a = a :=
    \choiceeq b \of A \by { existence: \exact(a, A), uniqueness: unique };
```

## choice eq wrong result

choice の等式証明を異なる結論の証明として使っている。

```toml case
id = "reject-system.choice_eq_wrong_result"
scope = "module"
expect = "reject"
name = "WrongResult"
parameters = '''A: \Set, a, b: A, unique: \forall (x, y: A) -> x = y'''
```

```ref
\definition bad: a = b :=
    \choiceeq a \of A \by { existence: \exact(a, A), uniqueness: unique };
```

## choice eq wrong uniqueness

choice の等式証明に別の性質の一意性証明を渡している。

```toml case
id = "reject-system.choice_eq_wrong_uniqueness"
scope = "module"
expect = "reject"
name = "WrongUniqueness"
parameters = '''A: \Set, a: A'''
```

```ref
\definition bad: a = a :=
    \choiceeq a \of A
      \by { existence: \exact(a, A), uniqueness: \fun (x, y: A) => \refl x };
```

## choice wrong existence

choice の存在証明が指定された性質の存在を示していない。

```toml case
id = "reject-system.choice_wrong_existence"
scope = "module"
expect = "reject"
name = "WrongExistence"
parameters = '''X, Y: \Set, existsY: \exists Y, unique: \forall (x, y: X) -> x = y'''
```

```ref
\definition bad: X := \choice X \by { existence: existsY, uniqueness: unique };
```

## choice wrong uniqueness

choice の一意性証明が指定された性質についての証明ではない。

```toml case
id = "reject-system.choice_wrong_uniqueness"
scope = "module"
expect = "reject"
name = "WrongUniqueness"
parameters = '''X: \Set, x: X, unique: \forall (a, b: X) -> a = a'''
```

```ref
\definition bad: X := \choice X \by { existence: \exact(x, X), uniqueness: unique };
```

## classical choice wrong inhabited

classical choice の inhabited 証明が別の集合についての証明である。

```toml case
id = "reject-system.classical_choice_wrong_inhabited"
scope = "module"
expect = "reject"
name = "ClassicalChoiceWrongInhabited"
parameters = '''X: \Set,
    Family: X -> \Set,
    wrong: \forall (x: X) -> \exists X,'''
```

```ref
\definition bad: \exists (\forall (x: X) -> Family x) :=
    \axiom:classicalIndefiniteChoice(X, Family, wrong);
```

## choice

存在と一意性の証明から対応する要素を選べる。

```toml case
id = "accept-system.choice"
scope = "module"
expect = "accept"
name = "ChoiceRules"
parameters = '''X: \Set, P: \Prop, predicate: X -> P, x: X,
    existsX: \exists X,
    uniqueX: \forall (x, y: X) -> x = y,
    anotherExistence: \exists X,
    anotherUniqueness: \forall (x, y: X) -> x = y,'''
```

```ref
\definition chosen: X :=
    \choice X \by { existence: existsX, uniqueness: uniqueX };
\definition chosen_property: P :=
    \take (y: X) => predicate y \by { existsX };
\definition chosen_property_block: P :=
    \block {
        \takefrom y: X \by existsX \then
        \return predicate y
    };
\definition chosen_at_x: x = chosen :=
    \choiceeq x \of X \by { existence: existsX, uniqueness: uniqueX };
\definition other_certificates: x = chosen :=
    \choiceeq x \of X
      \by { existence: anotherExistence, uniqueness: anotherUniqueness };
\definition recovered [a, b: X]: a = b :=
    \idelim chosen = b \with z: X => a = z
      \by { base: \choiceeq a \of X \by { existence: existsX, uniqueness: uniqueX },
        equality: \idelim b = chosen \with z: X => z = b
          \by { base: \refl b,
            equality: \choiceeq b \of X \by { existence: existsX, uniqueness: uniqueX } } };
```

## choice eq

choice の選んだ要素と一意な witness の等式を証明できる。

```toml case
id = "accept-system.choice_eq"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
/* Refinement membership, expected-set inference, macro traversal, and universes. */
\module ChoiceEquality(
    A: \Set, subset: \Pow A, a: \Cast[A] subset,
    existsA: \exists \Cast[A] subset,
    uniqueA: \forall (x, y: \Cast[A] subset) -> x = y,
) {
    \definition chosen: A :=
        \choice \Cast[A] subset \by { existence: existsA, uniqueness: uniqueA };
    \definition at_a: a = chosen :=
        \choiceeq a \of \Cast[A] subset \by { existence: existsA, uniqueness: uniqueA };
    \definition inferred_set: a = chosen :=
        \choiceeq a \of _ \by { existence: existsA, uniqueness: uniqueA };
    \definition member: \In[A] subset chosen :=
        \bysub(A, subset, \choice \Cast[A] subset \by { existence: existsA, uniqueness: uniqueA });
    \macro equal($element, $set) :=
        \choiceeq $element \of $set \by { existence: existsA, uniqueness: uniqueA };
    \definition macro_element [a: \Cast[A] subset]: a = chosen := equal!{a {\Cast[A] subset}};
    \macro choose($set) :=
        \choice $set \by { existence: existsA, uniqueness: uniqueA };
    \definition macro_choice: a = choose!{{\Cast[A] subset}} :=
        equal!{a {\Cast[A] subset}};
    \infer \choiceeq a \of \Cast[A] subset \by { existence: existsA, uniqueness: uniqueA };
}
\module HigherChoice(X: \Set(1), x: X, unique: \forall (a, b: X) -> a = b) {
    \definition chosen: X := \choice X \by { existence: \exact(x, X), uniqueness: unique };
    \definition at_x: x = chosen :=
        \choiceeq x \of X \by { existence: \exact(x, X), uniqueness: unique };
}
```

## nested choice

入れ子の choice でも各存在証明と一意性証明が対応する。

```toml case
id = "accept-system.nested_choice"
scope = "module"
expect = "accept"
name = "NestedChoice"
parameters = '''A: \Set, P: \Prop, a: A, hypothesis: P,
    existsEndo: \exists (A -> A),
    uniqueEndo: \forall (f, g: A -> A) -> f = g,
    X: \Set, existsX: \exists X, chooseProofEndo: X -> (P -> P),'''
```

```ref
\definition chosen_endo: A -> A :=
    \choice A -> A \by { existence: existsEndo, uniqueness: uniqueEndo };
\definition apply_chosen: A := chosen_endo a;
\definition directly_apply_choice: A :=
    (\choice A -> A \by { existence: existsEndo, uniqueness: uniqueEndo }) a;
\definition choice_under_application: A :=
    (\fun (f: A -> A) => f a)
    (\choice A -> A \by { existence: existsEndo, uniqueness: uniqueEndo });
\definition chosen_proof_endo: P -> P :=
    \take (y: X) => chooseProofEndo y \by { existsX };
\definition directly_apply_proof_take: P :=
    (\take (y: X) => chooseProofEndo y \by { existsX }) hypothesis;
\definition chosen_at_identity: (\fun (x: A) => x) = chosen_endo :=
    \choiceeq (\fun (x: A) => x) \of A -> A
      \by { existence: existsEndo, uniqueness: uniqueEndo };
```

