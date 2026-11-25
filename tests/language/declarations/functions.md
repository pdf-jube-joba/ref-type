# Structure-valued functions

## Structure-valued functions and field reduction

Applying a structure-returning function and projecting its fields reduces to values corresponding to the function arguments.

```toml case
id = "structure-valued-function-application"
scope = "module"
expect = "accept"
parameters = '''Carrier: \Set, x: Carrier'''
```

```ref
\structure Input[Carrier: \Set] := { value: Carrier };
\structure Output[Carrier: \Set] := { value: Carrier };
\definition convert[Carrier: \Set]: Input[Carrier] -> Output[Carrier] :=
  \fun (data: Input[Carrier]) => Output[Carrier] { value := data.value };
\definition choose[Carrier: \Set]: Input[Carrier] -> Input[Carrier] -> Output[Carrier] :=
  \fun (left, right: Input[Carrier]) => Output[Carrier] { value := right.value };
\definition make[Carrier: \Set]: Carrier -> Output[Carrier] :=
  \fun (value: Carrier) => Output[Carrier] { value := value };
\definition dependent: \forall (Carrier: \Set) -> Input[Carrier] -> Output[Carrier] :=
  \fun (Carrier: \Set) => \fun (data: Input[Carrier]) => Output[Carrier] { value := data.value };
\definition captured: \forall (value: Carrier) -> Output[Carrier] :=
  \fun (value: Carrier) => Output[Carrier] { value := (\fun (x: Carrier) => value) x };
\definition input: Input[Carrier] := Input[Carrier] { value := x };
\definition output: Output[Carrier] := convert[Carrier] input;
\definition chosen: Output[Carrier] := choose[Carrier] input input;
\definition made: Output[Carrier] := make[Carrier] x;
\definition dependentOutput: Output[Carrier] := dependent Carrier input;
\definition capturedOutput: Output[Carrier] := captured x;
\definition sameDependent: dependentOutput.value = x := \refl(x);
\definition sameCaptured: capturedOutput.value = x := \refl(x);
\definition same: output.value = x := \refl(x);
\definition sameChosen: chosen.value = x := \refl(x);
\definition sameMade: made.value = x := \refl(x);
```

## Parameter annotations of structure-valued functions

Even for a structure-returning function, a lambda parameter annotation differs from the domain.

```toml case
id = "structure-valued-lambda-annotation-mismatch"
scope = "module"
expect = "reject"
parameters = '''A: \Set, B: \Set'''
```

```ref
\structure Box[Carrier: \Set] := { value: Carrier };
\definition bad: A -> Box[B] := \fun (value: B) => Box[B] { value := value };
```

## Structure sort

A structure without an explicit sort is a signature. Adding a Set sort makes Cell a record that can be returned as a type.

```toml scenario
id = "structure-sort"
scope = "module"
```

```ref
\structure Cell[Carrier: \Set] := {
  value: Carrier,
};

\definition CellType: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => Cell[Carrier];
```

### Signature without a sort

A signature does not itself inhabit Set.

```toml step
id = "signature-has-no-sort"
expect = "reject"
```

### Record with an explicit sort

Adding an explicit Set sort makes Cell a record type.

```toml step
id = "record-has-sort"
expect = "accept"
```

```ref
\structure Cell[Carrier: \Set]: \Set := {
  value: Carrier,
};

\definition CellType: \forall (Carrier: \Set) -> \Set := \fun (Carrier: \Set) => Cell[Carrier];
```

## Structure value projection

Packed.value is a projection function, while data.value is the field of a particular record. The law must compare field values from that record.

```toml scenario
id = "structure-value-projection"
scope = "module"
```

```ref
\structure Packed: \SetKind := {
  Carrier: \Set,
  value: Carrier,
};

\structure Laws := {
  data: Packed,
  reflexive: Packed.value = Packed.value,
};
```

### Projecting from the record type

Packed.value still needs a record argument, so it cannot be used as the element compared by this equality.

```toml step
id = "project-from-type"
expect = "reject"
```

### Projecting from the record value

Projecting data.value gives the field of the supplied record.

```toml step
id = "project-from-value"
expect = "accept"
```

```ref
\structure Packed: \SetKind := {
  Carrier: \Set,
  value: Carrier,
};

\structure Laws := {
  data: Packed,
  reflexive: data.value = data.value,
};
```

## Sorts of generated projections

The projection's product does not satisfy the permitted sort relation.

```toml case
id = "generated-projection"
scope = "module"
expect = "reject"
```

```ref
\structure Bad: \Prop := { b: \Prop };
```
