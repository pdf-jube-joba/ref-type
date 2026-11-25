# Conversion and reduction regressions

## Display conversion

Definitional equality checking also works for terms with display information.

```toml case
id = "display-conversion"
scope = "module"
expect = "accept"
name = "Display"
```

```ref
\inductive Index: \Set := | zero: Index | one: Index;
\inductive Item: \Set := | value: Item;
\definition IndexedValue[k: Index]: \Set := Item;
\definition forgetIndex[k: Index][value: IndexedValue k]: Item := value;
\definition atIndex[k: Index][representation: Item]: IndexedValue k := representation;
\definition changeIndex[k, l: Index][value: IndexedValue k]: IndexedValue l := atIndex l (forgetIndex k value);
\definition transport[k, l: Index][value: IndexedValue k][same: k = l]: IndexedValue l := changeIndex k l value;
\definition identity: \forall (k: Index)(value: IndexedValue k)(same: k = k) -> transport k k value same = value :=
  \fun (k: Index)(value: IndexedValue k)(same: k = k) => \refl value;
```

## Inductive reduction large parameter

Recursor reduction preserves types even for inductive types with large parameters.

```toml case
id = "inductive-reduction-large-parameter"
scope = "module"
expect = "accept"
name = "InductiveReductionLargeParameter"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive Pair[A, B: \Set]: \Set := | pair: A -> B -> Pair;
\definition first [A, B: \Set] [p: Pair[A, B]]: A :=
  \induction (p: Pair[A, B]) \return A \with {
    | pair: \fun (a: A) => \fun (b: B) => a
  } p;
\definition T0: \Set := Unit;
\definition T1: \Set := Pair[T0, T0];
\definition T2: \Set := Pair[T1, T1];
\definition T3: \Set := Pair[T2, T2];
\definition T4: \Set := Pair[T3, T3];
\definition T5: \Set := Pair[T4, T4];
\definition T6: \Set := Pair[T5, T5];
\definition T7: \Set := Pair[T6, T6];
\definition T8: \Set := Pair[T7, T7];
\definition project [x: T8]: first T8 T8 (Pair[T8, T8]::pair x x) = x := \refl(x);
```

## Refined function application

Application of a function with refinements has the corresponding type.

```toml case
id = "refined-function-application"
scope = "module"
expect = "accept"
name = "RefinedFunctionApplication"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\inductive True: \Prop := | yes: True;
\definition Functions: \Pow (Unit -> Unit) := { f : Unit -> Unit \where True };
\definition identity: \Cast[Unit -> Unit] (Functions) :=
  \into[Unit -> Unit](\fun (x: Unit) => x, Functions) \by { True::yes };
\definition identityBeta [x: Unit]: identity x = x := \refl(x);
```

