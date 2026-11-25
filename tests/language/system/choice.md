# Choice and uniqueness

## Choice eq wrong element

The element passed to the choice equality proof does not belong to the specified set.

```toml case
id = "choice-eq-wrong-element"
scope = "module"
expect = "reject"
name = "WrongElement"
parameters = '''A, B: \Set, a: A, b: B, unique: \forall (x, y: A) -> x = y'''
```

```ref
\definition bad: a = a :=
    \choiceeq b \of A \by { existence: \exact(a, A), uniqueness: unique };
```

## Choice eq wrong result

The choice equality proof is used to prove a different conclusion.

```toml case
id = "choice-eq-wrong-result"
scope = "module"
expect = "reject"
name = "WrongResult"
parameters = '''A: \Set, a, b: A, unique: \forall (x, y: A) -> x = y'''
```

```ref
\definition bad: a = b :=
    \choiceeq a \of A \by { existence: \exact(a, A), uniqueness: unique };
```

## Choice eq wrong uniqueness

A uniqueness proof for a different property is passed to the choice equality proof.

```toml case
id = "choice-eq-wrong-uniqueness"
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

## Choice wrong existence

The choice existence proof does not establish existence for the specified property.

```toml case
id = "choice-wrong-existence"
scope = "module"
expect = "reject"
name = "WrongExistence"
parameters = '''X, Y: \Set, existsY: \exists Y, unique: \forall (x, y: X) -> x = y'''
```

```ref
\definition bad: X := \choice X \by { existence: existsY, uniqueness: unique };
```

## Choice wrong uniqueness

The choice uniqueness proof does not concern the specified property.

```toml case
id = "choice-wrong-uniqueness"
scope = "module"
expect = "reject"
name = "WrongUniqueness"
parameters = '''X: \Set, x: X, unique: \forall (a, b: X) -> a = a'''
```

```ref
\definition bad: X := \choice X \by { existence: \exact(x, X), uniqueness: unique };
```

## Classical choice wrong inhabited

The inhabited proof for classical choice concerns a different set.

```toml case
id = "classical-choice-wrong-inhabited"
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

## Choice and interchangeable proof certificates

Corresponding elements can be selected from existence and uniqueness proofs.

```toml case
id = "choice-and-certificate-erasure"
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

## Choice equality through refinements and macros

Equality between the chosen element and the unique witness can be proved.

```toml case
id = "choice-equality-through-refinements-and-macros"
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

## Nested choice

Existence and uniqueness proofs also correspond in nested choices.

```toml case
id = "nested-choice"
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

