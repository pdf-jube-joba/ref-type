# Program type-associated items

## Constructor name collision

An associated item name conflicts with a constructor.

```toml case
id = "constructor-name-collision"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\definition Unit::unit: Unit := Unit::unit;
```

## Dependent field

A Program record field's type depends on an earlier field's value.

```toml case
id = "dependent-field"
scope = "module"
expect = "reject"
```

```ref
\structure Dep[A: \VType]: \VType := { first: A, second: first };
```

## Duplicate declaration field

A Program record declaration duplicates a field name.

```toml case
id = "duplicate-declaration-field"
scope = "module"
expect = "reject"
```

```ref
\structure Dup[A: \VType]: \VType := { first: A, first: A };
```

## Duplicate field

A Program record literal specifies the same field twice.

```toml case
id = "duplicate-field"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Unit::unit, first := Unit::unit, second := Unit::unit };
```

## Inductive literal

An inductive type that is not a Program record is used as a record literal.

```toml case
id = "inductive-literal"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\definition bad: Unit := Unit {};
```

## Missing field

A Program record literal lacks required fields.

```toml case
id = "missing-field"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Unit::unit };
```

## Owner parameter count

The number of associated-item owner arguments does not match the declaration.

```toml case
id = "owner-parameter-count"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair::value: Unit := Unit::unit;
```

## Owner parameter kind

A Program associated item's owner argument is not classified as VType.

```toml case
id = "owner-parameter-kind"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair[A: \Set]::value: Unit := Unit::unit;
```

## Projection as value

An associated projection is used as a Program value.

```toml case
id = "projection-as-value"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\check Pair[Unit]::first: \U(Pair[Unit] ~> \F(Unit));
```

## Projection name collision

An associated item name conflicts with a generated projection.

```toml case
id = "projection-name-collision"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair[A: \VType]::first: \F(Unit) := \return Unit::unit;
```

## Recursive field

A Program record field's type references the type being declared.

```toml case
id = "recursive-field"
scope = "module"
expect = "reject"
```

```ref
\structure Rec: \VType := { next: Rec };
```

## Type argument count

The number of associated-item type arguments does not match the declaration.

```toml case
id = "type-argument-count"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\infer Pair[Unit, Unit]::first;
```

## Unknown field

A nonexistent Program record field is specified.

```toml case
id = "unknown-field"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Unit::unit, second := Unit::unit, third := Unit::unit };
```

## Unsolved type argument

An associated item's type arguments cannot be inferred.

```toml case
id = "unsolved-type-argument"
scope = "module"
expect = "reject"
```

```ref
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\infer Pair::first;
```

## Unused invalid item

An unused associated item also has a type mismatch.

```toml case
id = "unused-invalid-item"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair[A: \VType]::bad: Pair[A] ~> \F(Unit) := \cfun (p: Pair[A]) => \return p;
```

## Value as computation

A Program value is used as a computation.

```toml case
id = "value-as-computation"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\definition Unit::value: Unit := Unit::unit;
\check Unit::value: \F(Unit);
```

## Wrong field type

A Program record field value does not have the declared type.

```toml case
id = "wrong-field-type"
scope = "module"
expect = "reject"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Bool::no, second := Unit::unit };
```

## Associated order

Program associated items can be used in declaration order.

```toml case
id = "associated-order"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source {
  \inductive First: \VType := | first: First;
  \inductive Second: \VType := | second: Second;
  \definition second: Second := Second::second;
  \definition First::second: Second := second;
}
\module Consumer {
  \import \root.Source[] \as S;
  \check S.First::second: S.Second;
}
```

## Certificates

A Program associated computation uses a termination certificate at either constructor of its state type, and remains executable after module import and boxing.

```toml case
id = "certificates"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module CertifiedSteps {
  \inductive Bit: \VType := | zero: Bit | one: Bit;
  \structure Owner[A: \VType]: \VType := {};
  \definition step: \U((Bit ~> \F(\RunStep[Bit, Bit]))) :=
    \thunk((\cfun (s: Bit) => \return(\finish[Bit, Bit](Bit::zero))));

  \definition Terminates [s: Bit^]: \Prop :=
    \forall (P: Bit^ -> \Prop) ->
      (\forall (x: Bit^) ->
        (\step-match t: \RunStep[Bit^, Bit^] \return \Prop \with {
          | \continue next: P next
          | \finish output: \forall (Q: \Prop) -> Q -> Q
        }) (step^ x) -> P x) -> P s;
  \definition terminates: \forall (s: Bit^) -> Terminates s :=
    \fun (s: Bit^) (P: _) (h: _) => h s (\fun (Q: \Prop) (q: Q) => q);
  \definition Owner[A: \VType]::result: \F(Bit) :=
    \run[Bit, Bit](step, Bit::zero) \by { terminates Bit^::zero };
  \definition Owner[A: \VType]::otherResult: \F(Bit) :=
    \run[Bit, Bit](step, Bit::one) \by { terminates Bit^::one };
  \definition boxed: \Box[\F(Bit)] := \box[_](Owner[Bit]::result);
}

\module CertifiedConsumer {
  \import \root.CertifiedSteps[] \as S;
  \definition boxed: \Box[\F(S.Bit)] := \box[_](S.Owner[S.Bit]::result);
  \normalize \squash[_](boxed);
  \normalize S.Owner[S.Bit]::result;
}
```

## Program module instantiation and re-exports

Instantiation and re-export of Program modules preserve member types.

```toml case
id = "program-module-instantiation-and-reexports"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source(X: \VType, x: X) {
  \structure Duo[A, B: \VType]: \VType := { left: A, right: B };
  \definition Duo[A, B: \VType]::make[a: A, b: B]: \F(Duo[A, B]) :=
    \return Duo[A, B] { left := a, right := b };
  \definition Duo[A, B: \VType]::left_again: Duo[A, B] ~> \F(A) := Duo[A, B]::left;
  \definition Duo[A, B: \VType]::get_x: X := x;
  \structure Empty: \VType := {};
  \definition Empty::empty: Empty := Empty {};
  \structure Thunked[A: \VType]: \VType := { thunk: \U(A ~> \F(A)) };
  \definition Thunked[A: \VType]::identity: Thunked[A] := Thunked[A] {
    thunk := \thunk (\cfun (a: A) => \return a)
  };
  \inductive List[A: \VType]: \VType := | nil: List | cons: A -> List[A] -> List;
  \definition List[A: \VType]::empty: List[A] := List[A]::nil;
  \definition List[A: \VType]::is_empty[xs: List[A]]: \F(X) :=
    \match xs \in List \with { | nil : \return x | cons a rest : \return x };
  \definition List[A: \VType]::singleton[a: A]: \F(List[A]) :=
    \return List[A]::cons a List[A]::empty;
}
\module Consumer {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Source[X := Unit, x := Unit::unit] \as S;
  \check S.Duo[Unit, Unit]::get_x: Unit;
  \check S.List[Unit]::is_empty S.List[Unit]::empty: \F(Unit);
  \check S.Empty::empty: S.Empty;
  \check S.Duo[Unit, Unit]::make Unit::unit Unit::unit: \F(S.Duo[Unit, Unit]);
  \normalize S.Duo[Unit, Unit]::make Unit::unit Unit::unit;
  \normalize
    \bind f: \U(Unit ~> \F(Unit)) <- S.Thunked[Unit]::thunk S.Thunked[Unit]::identity \in
    \force f Unit::unit;
  \normalize S.List[Unit]::singleton Unit::unit;
  \definition package: \Box[S.Duo[Unit, Unit] ~> \F(Unit)] := \box[_](S.Duo[Unit, Unit]::left_again);
  \normalize \squash[_](package);
}

\module Reexport(X: \VType, x: X) {
  \import \root.Source[X := X, x := x] \as S;
  \definition empty: S.Empty := S.Empty::empty;
  \definition identity[a: X]: \F(X) := \return a;
}
\module Again {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Reexport[X := Unit, x := Unit::unit] \as R;
  \import \root.Source[X := Unit, x := Unit::unit] \as S1;
  \import \root.Source[X := Unit, x := Unit::unit] \as S2;
  \check S1.Empty::empty: S1.Empty;
  \check S2.Empty::empty: S2.Empty;
  \definition same: S2.Empty := S1.Empty::empty;
  \definition through_outer: S1.Empty := R.empty;
  \normalize R.identity Unit::unit;
}
```

## Namespace identity

Types extracted from the same nominal instantiation retain their identity.

```toml case
id = "namespace-identity"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source {
  \structure Empty: \VType := {};
  \definition Empty::empty: Empty := Empty {};
}
\module Consumer {
  \import \root.Source[] \as Left;
  \import \root.Source[] \as Right;
  \definition same: Right.Empty := Left.Empty::empty;
}
```

## Set owners expose reflected Program values

An associated item of a Set record can expose the reflected value of a Program constructor.

```toml case
id = "set-owner-exposes-reflected-program-value"
scope = "module"
expect = "accept"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\structure Holder: \Set := {};
\definition Holder::value: Unit^ := Unit^::unit;
\check Holder::value: Unit^;
```

## Program record construction and projections

Program record fields, projections, and cases have corresponding types.

```toml case
id = "program-record-construction-and-projections"
scope = "module"
expect = "accept"
```

```ref
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair[A: \VType]::swap: Pair[A] ~> \F(Pair[A]) :=
  \cfun (p: Pair[A]) => (\bind x: A <- (Pair::first p) \in
    \bind y: A <- ((Pair[_]::second) p) \in
    \return Pair[A] { first := y, second := x });
\definition Pair[A: \VType]::swap_thunk: \U(Pair[A] ~> \F(Pair[A])) := \thunk (Pair[A]::swap);
\definition pair: Pair[Bool] := Pair[Bool] { second := Bool::yes, first := Bool::no };
\definition first: \F(Bool) := ((Pair[Bool]::first) pair);
\definition swapped: \F(Pair[Bool]) := ((Pair[Bool]::swap) pair);
\normalize first;
\normalize ((Pair[Bool]::swap) pair);
\check (Pair::first pair): \F(Bool);
\check ((Pair[_]::second) pair): \F(Bool);
\check Pair { first := Bool::yes, second := Bool::no }: Pair[Bool];
\check Pair::swap_thunk: \U(Pair[Bool] ~> \F(Pair[Bool]));
\normalize ((\force Pair[Bool]::swap_thunk) pair);
```

