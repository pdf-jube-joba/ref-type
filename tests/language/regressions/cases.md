# regressions / cases

## display conversion

表示を伴う項でも定義的等価性の検査が成立する。

```toml case
id = "accept-regressions.display_conversion"
scope = "module"
expect = "accept"
name = "Display"
```

```ref
\inductive Degree: \Set := | zero: Degree | one: Degree;
\inductive Scalar: \Set := | value: Scalar;
\definition Form[k: Degree]: \Set := Scalar;
\definition series[k: Degree][omega: Form k]: Scalar := omega;
\definition recover[k: Degree][representation: Scalar]: Form k := representation;
\definition convert[k, l: Degree][omega: Form k]: Form l := recover l (series k omega);
\definition cast[k, l: Degree][omega: Form k][same: k = l]: Form l := convert k l omega;
\definition identity: \forall (k: Degree)(omega: Form k)(same: k = k) -> cast k k omega same = omega :=
  \fun (k: Degree)(omega: Form k)(same: k = k) => \refl omega;
```

## inductive reduction large parameter

大きな parameter を持つ帰納型でも再帰子の簡約が型を保つ。

```toml case
id = "accept-regressions.inductive_reduction_large_parameter"
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

## refined function application

refinement を持つ関数の application が対応する型を持つ。

```toml case
id = "accept-regressions.refined_function_application"
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

