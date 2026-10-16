# program-items / cases

## constructor name collision

associated item の名前が constructor と衝突している。

```toml case
id = "reject-program-items.constructor-name-collision"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Unit::unit: Unit := Unit::unit;
```

## dependent field

Program record の field 型が先行する field の値に依存する。

```toml case
id = "reject-program-items.dependent-field"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\structure Dep[A: \VType]: \VType := { first: A, second: first };
```

## duplicate declaration field

Program record の宣言で field 名が重複している。

```toml case
id = "reject-program-items.duplicate-declaration-field"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\structure Dup[A: \VType]: \VType := { first: A, first: A };
```

## duplicate field

Program record の literal で同じ field を二度指定している。

```toml case
id = "reject-program-items.duplicate-field"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Unit::unit, first := Unit::unit, second := Unit::unit };
```

## inductive literal

Program record ではない帰納型を record literal として使っている。

```toml case
id = "reject-program-items.inductive-literal"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Unit := Unit {};
```

## missing field

Program record の literal に必要な field が不足している。

```toml case
id = "reject-program-items.missing-field"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Unit::unit };
```

## owner parameter count

associated item の owner 引数の数が宣言と一致しない。

```toml case
id = "reject-program-items.owner-parameter-count"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair::value: Unit := Unit::unit;
```

## owner parameter kind

Program associated item の owner 引数が VType に分類されない。

```toml case
id = "reject-program-items.owner-parameter-kind"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair(A: \Set)::value: Unit := Unit::unit;
```

## projection as value

associated projection を Program value として使っている。

```toml case
id = "reject-program-items.projection-as-value"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\check Pair[Unit]::first: \U(Pair[Unit] ~> \F(Unit));
```

## projection name collision

associated item の名前が生成される projection と衝突する。

```toml case
id = "reject-program-items.projection-name-collision"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair(A: \VType)::first: \F(Unit) := \return Unit::unit;
```

## recursive field

Program record の field 型が宣言中の型を参照する。

```toml case
id = "reject-program-items.recursive-field"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\structure Rec: \VType := { next: Rec };
```

## type argument count

associated item の型引数の数が宣言と一致しない。

```toml case
id = "reject-program-items.type-argument-count"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\infer Pair[Unit, Unit]::first;
```

## unknown field

Program record に存在しない field を指定する。

```toml case
id = "reject-program-items.unknown-field"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Unit::unit, second := Unit::unit, third := Unit::unit };
```

## unsolved type argument

associated item の型引数を推論できない。

```toml case
id = "reject-program-items.unsolved-type-argument"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\infer Pair::first;
```

## unused invalid item

使われない associated item にも型の不一致がある。

```toml case
id = "reject-program-items.unused-invalid-item"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair(A: \VType)::bad: Pair[A] ~> \F(Unit) := \cfun (p: Pair[A]) => \return p;
```

## value as computation

Program value を computation として使っている。

```toml case
id = "reject-program-items.value-as-computation"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Unit::value: Unit := Unit::unit; \check Unit::value: \F(Unit);
```

## wrong field type

Program record の field 値が宣言された型を持たない。

```toml case
id = "reject-program-items.wrong-field-type"
scope = "module"
expect = "reject"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition bad: Pair[Unit] := Pair[Unit] { first := Bool::no, second := Unit::unit };
```

## associated order

Program associated item を宣言順に利用できる。

```toml case
id = "accept-program-items.associated-order"
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

## certificates

Program の実装とその仕様に対応する証明書を構築できる。

```toml case
id = "accept-program-items.certificates"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module CertifiedSteps {
          \inductive Unit: \VType := | unit: Unit | other: Unit;
          \structure Owner[A: \VType]: \VType := {};
          \definition step: \U((Unit ~> \F(\RunStep[Unit, Unit]))) :=
            \thunk((\cfun (s: Unit) => \return(\finish[Unit, Unit](Unit::unit))));
          
          \definition Terminates (s: Unit^): \Prop :=
            \forall (P: Unit^ -> \Prop) ->
              (\forall (x: Unit^) ->
                (\step-match t: \RunStep[Unit^, Unit^] \return \Prop \with {
                  | \continue next: P next
                  | \finish output: \forall (Q: \Prop) -> Q -> Q
                }) (step^ x) -> P x) -> P s;
          \definition terminates: \forall (s: Unit^) -> Terminates s :=
            \fun (s: Unit^) (P: _) (h: _) => h s (\fun (Q: \Prop) (q: Q) => q);
          \definition Owner(A: \VType)::result: \F(Unit) :=
            \run[Unit, Unit](step, Unit::unit) \by { terminates Unit^::unit };
          \definition Owner(A: \VType)::otherResult: \F(Unit) :=
            \run[Unit, Unit](step, Unit::other) \by { terminates Unit^::other };
          \definition boxed: \Box[\F(Unit)] := \box[_](Owner[Unit]::result);
        }

\module CertifiedConsumer {
  \import \root.CertifiedSteps[] \as S;
  \definition boxed: \Box[\F(S.Unit)] := \box[_](S.Owner[S.Unit]::result);
  \normalize \squash[_](boxed);
  \normalize S.Owner[S.Unit]::result;
}
```

## modules

Program module の具体化と再 export が member の型を保つ。

```toml case
id = "accept-program-items.modules"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source(X: \VType, x: X) {
  \structure Duo[A, B: \VType]: \VType := { left: A, right: B };
  \definition Duo(A, B: \VType)::make(a: A, b: B): \F(Duo[A, B]) :=
    \return Duo[A, B] { left := a, right := b };
  \definition Duo(A, B: \VType)::left_again: Duo[A, B] ~> \F(A) := Duo[A, B]::left;
  \definition Duo(A, B: \VType)::get_x: X := x;
  \structure Empty: \VType := {};
  \definition Empty::empty: Empty := Empty {};
  \structure Thunked[A: \VType]: \VType := { thunk: \U(A ~> \F(A)) };
  \definition Thunked(A: \VType)::identity: Thunked[A] := Thunked[A] {
    thunk := \thunk (\cfun (a: A) => \return a)
  };
  \inductive List[A: \VType]: \VType := | nil: List | cons: A -> List[A] -> List;
  \definition List(A: \VType)::empty: List[A] := List[A]::nil;
  \definition List(A: \VType)::is_empty(xs: List[A]): \F(X) :=
    \match xs \in List \with { | nil : \return x | cons a rest : \return x };
  \definition List(A: \VType)::singleton(a: A): \F(List[A]) :=
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
  \definition identity(a: X): \F(X) := \return a;
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

## namespace identity

同じ nominal な具体化から取り出した型の同一性を保つ。

```toml case
id = "accept-program-items.namespace-identity"
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

## pts associated owner

PTS の型を owner 引数に持つ associated item を使える。

```toml case
id = "accept-program-items.pts-associated-owner"
scope = "module"
expect = "accept"
name = "Bad"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\structure P: \Set := {}; \definition P::value: Unit^ := Unit^::unit;
```

## records

Program record の field と projection と case の型が対応する。

```toml case
id = "accept-program-items.records"
scope = "module"
expect = "accept"
name = "Example"
```

```ref
\inductive Bool: \VType := | no: Bool | yes: Bool;
\structure Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair(A: \VType)::swap: Pair[A] ~> \F(Pair[A]) :=
  \cfun (p: Pair[A]) => (\bind x: A <- (Pair::first p) \in
    \bind y: A <- ((Pair[_]::second) p) \in
    \return Pair[A] { first := y, second := x });
\definition Pair(A: \VType)::swap_thunk: \U(Pair[A] ~> \F(Pair[A])) := \thunk (Pair[A]::swap);
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

