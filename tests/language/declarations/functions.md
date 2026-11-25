# language / declarations / functions

## structure result arrows check lambdas and their applications

Applying a structure-returning function and projecting its fields reduces to values corresponding to the function arguments.

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

Even for a structure-returning function, a lambda parameter annotation differs from the domain.

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

A structure without an explicit sort is treated as a signature; a structure with an explicit sort can be used as a type.

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

It cannot be used as a type.

```toml step
id = "invalid"
expect = "reject"
```

### value

Specifying the required sort or value makes it accepted.

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

Value fields cannot be extracted from a structure type itself; extracting them from a structure value data allows equalities to be stated.

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

It cannot be used as a type.

```toml step
id = "invalid"
expect = "reject"
```

### value

Specifying the required sort or value makes it accepted.

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

## Sorts of generated projections

The projection's product does not satisfy the permitted sort relation.

```toml case
id = "generated-projection"
scope = "module"
expect = "reject"
name = "M"
```

```ref
\structure Bad: \Prop := { b: \Prop };
```
