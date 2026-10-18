# language / declarations / functions

## structure result arrows check lambdas and their applications

structure を返す関数の application と field の射影は、関数の引数に対応する値に簡約される。

```toml case
id = "structure_result_arrows_check_lambdas_and_their_applications"
scope = "module"
expect = "accept"
name = "Playground"
parameters = '''Carrier: \Set, x: Carrier'''
```

```ref
\structure A[Carrier: \Set] := { a: Carrier };
\structure B[Carrier: \Set] := { b: Carrier };
\definition AtoB[Carrier: \Set]: A[Carrier] -> B[Carrier] :=
  \fun (data: A[Carrier]) => B[Carrier] { b := data.a };
\definition choose[Carrier: \Set]: A[Carrier] -> A[Carrier] -> B[Carrier] :=
  \fun (left, right: A[Carrier]) => B[Carrier] { b := right.a };
\definition make[Carrier: \Set]: Carrier -> B[Carrier] :=
  \fun (value: Carrier) => B[Carrier] { b := value };
\definition dependent: \forall (Carrier: \Set) -> A[Carrier] -> B[Carrier] :=
  \fun (Carrier: \Set) => \fun (data: A[Carrier]) => B[Carrier] { b := data.a };
\definition captured: \forall (value: Carrier) -> B[Carrier] :=
  \fun (value: Carrier) => B[Carrier] { b := (\fun (x: Carrier) => value) x };
\definition input: A[Carrier] := A[Carrier] { a := x };
\definition output: B[Carrier] := AtoB[Carrier] input;
\definition chosen: B[Carrier] := choose[Carrier] input input;
\definition made: B[Carrier] := make[Carrier] x;
\definition dep: B[Carrier] := dependent Carrier input;
\definition cap: B[Carrier] := captured x;
\definition sameDependent: dep.b = x := \refl(x);
\definition sameCaptured: cap.b = x := \refl(x);
\definition same: output.b = x := \refl(x);
\definition sameChosen: chosen.b = x := \refl(x);
\definition sameMade: made.b = x := \refl(x);
```

## structure result lambdas check their parameter annotations

structure を返す関数でも、lambda の parameter 注釈が domain と異なる。

```toml case
id = "structure_result_lambdas_check_their_parameter_annotations"
scope = "module"
expect = "reject"
name = "M"
parameters = '''A: \Set, B: \Set'''
```

```ref
\structure Box[Carrier: \Set] := { value: Carrier };
\definition bad: A -> Box[B] := \fun (value: B) => Box[B] { value := value };
```

## structure sort

sort を省いた structure は signature として扱う。sort を指定した structure は型として利用できる。

```toml scenario
id = "structure-sort"
scope = "module"
name = "Playground"
```

```ref
\structure A[Carrier: \Set] := {
  op1: Carrier,
};

\definition F: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => A[Carrier];
```

### signature

型として利用できない。

```toml step
id = "invalid"
expect = "reject"
```

### value

必要な sort または値を指定すると受理される。

```toml step
id = "fixed"
expect = "accept"
```

```ref
\structure A[Carrier: \Set]: \Set := {
  op1: Carrier,
};

\definition F: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => A[Carrier];
```

## structure value projection

structure の型自体から値の field は取り出せない。structure の値 data から field を取り出すと等式を記述できる。

```toml scenario
id = "structure-value-projection"
scope = "module"
name = "Playground"
```

```ref
\structure A: \SetKind := {
  Carrier: \Set,
  a: Carrier,
};

\structure ALaw := {
  data: A,
  some: A.a = A.a,
};
```

### signature

型として利用できない。

```toml step
id = "invalid"
expect = "reject"
```

### value

必要な sort または値を指定すると受理される。

```toml step
id = "fixed"
expect = "accept"
```

```ref
\structure A: \SetKind := {
  Carrier: \Set,
  a: Carrier,
};

\structure ALaw := {
  data: A,
  some: data.a = data.a,
};
```

## 生成される projection の sort

projection の積が許可された sort 関係を満たさない。

```toml case
id = "generated-projection"
scope = "module"
expect = "reject"
name = "M"
```

```ref
\structure Bad: \Prop := { b: \Prop };
```
