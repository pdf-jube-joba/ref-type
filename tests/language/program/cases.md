# program / cases

## boxed value

Box の引数が Program の computation type になっていないため、拒否される。

```toml case
id = "reject-boxed-value"
scope = "module"
expect = "reject"
name = "BoxedValue"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\definition bad: \Box[Unit] := \box[_](Unit::unit);
```

## program cbv ambiguous application

Program の関数 value を force せずに application しているため、拒否される。

```toml case
id = "reject-program-cbv-ambiguous-application"
scope = "module"
expect = "reject"
name = "ProgramCbvAmbiguousApplication"
parameters = '''A: \VType, a: A'''
```

```ref
\definition bad(f: _): _ := f a;
```

## program cbv computation argument

value を要求する引数位置に computation を渡しているため、拒否される。

```toml case
id = "reject-program-cbv-computation-argument"
scope = "module"
expect = "reject"
name = "ProgramCbvComputationArgument"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\definition identity: Bool -> Bool := \fun (x: Bool) => \return(x);
\definition bad: \F(Bool) := identity (identity Bool::true);
```

## program cbv computation codomain

Program の関数の codomain が computation type になっていないため、拒否される。

```toml case
id = "reject-program-cbv-computation-codomain"
scope = "module"
expect = "reject"
name = "ProgramCbvComputationCodomain"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\definition bad: Bool -> \F(Bool) :=
  \fun (x: Bool) => \return(x);
```

## program cbv dependent arrow

Program の arrow の codomain が値に依存しているため、拒否される。

```toml case
id = "reject-program-cbv-dependent-arrow"
scope = "module"
expect = "reject"
name = "ProgramCbvDependentArrow"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\definition bad: \forall (x: Bool) -> \F(Bool) :=
  \cfun (x: Bool) => \return(x);
```

## program cbv non function application

Program の関数ではない value を application しているため、拒否される。

```toml case
id = "reject-program-cbv-non-function-application"
scope = "module"
expect = "reject"
name = "ProgramCbvNonFunctionApplication"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\definition value: Bool := Bool::true;
\definition bad: \F(Bool) := value Bool::false;
```

## program implicit bind

computation の結果を bind せず value として使っているため、拒否される。

```toml case
id = "reject-program-implicit-bind"
scope = "module"
expect = "reject"
name = "ProgramImplicitBind"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\definition first: Bool -> Bool -> Bool :=
  \fun (x, y: Bool) => \return(x);
\definition bad: \F(Bool) := first Bool::true Bool::false;
```

## program implicit force

thunk を force せず computation として使っているため、拒否される。

```toml case
id = "reject-program-implicit-force"
scope = "module"
expect = "reject"
name = "ProgramImplicitForce"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\definition apply(f: \U(Bool ~> \F(Bool)), x: Bool): \F(Bool) := f x;
```

## program module parameter wrong category

module parameter の value と computation の分類が一致しないため、拒否される。

```toml case
id = "reject-program-module-parameter-wrong-category"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Source(X: \VType, x: X) {}
\module Bad {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Source[X := Unit, x := Unit] \as S;
}
```

## program module parameter wrong value

module parameter に渡した Program value の型が一致しないため、拒否される。

```toml case
id = "reject-program-module-parameter-wrong-value"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Source(X: \VType, x: X) {}
\module Bad {
  \inductive Left: \VType := | left: Left;
  \inductive Right: \VType := | right: Right;
  \import \root.Source[X := Left, x := Right::right] \as S;
}
```

## program cbv syntax sugar

Program の surface syntax を value と computation の型に従って展開できるため、受理される。

```toml case
id = "accept-program-cbv-syntax-sugar"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ProgramCbvSyntaxSugar {
  \inductive Bool: \VType :=
  | false: Bool
  | true: Bool
  ;
  \inductive Holder: \VType :=
  | hold: (Bool -> Bool) -> Holder
  ;

  /* The new type and lambda elaborate to the explicit CBPV definition. */
  \definition andExplicit: Bool ~> \F(\U(Bool ~> \F(Bool))) :=
    \cfun (x: Bool) => \return(\thunk(\cfun (y: Bool) =>
      \match x \in Bool \with {
      | false : \return(Bool::false)
      | true : \return(y)
      }));

  \definition and: Bool -> Bool -> Bool :=
    \fun (x, y: Bool) =>
      \match x \in Bool \with {
      | false : \return(Bool::false)
      | true : \return(y)
      };
  \definition newTypeOldBody: Bool -> Bool :=
    \cfun (x: Bool) => \return(x);
  \definition oldTypeNewBody: Bool ~> \F(Bool) :=
    \fun (x: Bool) => \return(x);
  \definition mixedArrow: Bool ~> (Bool -> Bool) :=
    \cfun (x: Bool) => \fun (y: Bool) => \return(y);

  /* A value-position lambda is thunked; applying the resulting value requires force. */
  \definition identity: \U(Bool -> Bool) :=
    \thunk(\fun (x: Bool) => \return(x));
  \definition holder: Holder := Holder::hold (\fun (x: Bool) => \return(x));
  \definition apply(f: Bool -> Bool, x: Bool): \F(Bool) := (\force f) x;
  \definition applyExplicit(f: \U(Bool ~> \F(Bool)), x: Bool): \F(Bool) :=
    (\force f) x;
  \definition shadow(and: Bool -> Bool, x: Bool): \F(Bool) := (\force and) x;

  /* Curried CBV application spells out sequencing and forcing. */
  \definition falseAndTrue: \F(Bool) :=
    \bind next: Bool -> Bool <- and Bool::false \in
    (\force next) Bool::true;
  \definition falseAndTrueExplicit: \F(Bool) :=
    \bind next: Bool -> Bool <- and Bool::false \in
    (\force next) Bool::true;
  \definition trueAndFalse: \F(Bool) :=
    \bind next: Bool -> Bool <- andExplicit Bool::true \in
    (\force next) Bool::false;
  \definition partial: \F(Bool -> Bool) := and Bool::true;
  \definition fromPartial: \F(Bool) :=
    \bind next: Bool -> Bool <- partial \in
    (\force next) Bool::false;

  \definition choose3: Bool -> Bool -> Bool -> Bool :=
    \fun (x: Bool) => \fun (y, z: Bool) =>
      \match x \in Bool \with {
      | false : \return(y)
      | true : \return(z)
      };
  \definition choose3Explicit:
      Bool ~> \F(\U(Bool ~> \F(\U(Bool ~> \F(Bool))))) :=
    \cfun (x: Bool) => \return(\thunk(
      \cfun (y: Bool) => \return(\thunk(
        \cfun (z: Bool) =>
          \match x \in Bool \with {
          | false : \return(y)
          | true : \return(z)
          }))));
  \definition chosen: \F(Bool) :=
    \bind second: Bool -> Bool -> Bool <- choose3 Bool::true \in
    \bind third: Bool -> Bool <- (\force second) Bool::false \in
    (\force third) Bool::true;

  \check (\fun (x: Bool) => \return(x)): Bool -> Bool;
  \check (\fun (x: Bool) => \return(x)): \U(Bool -> Bool);
  \check apply (\fun (x: Bool) => \return(x)) Bool::true: \F(Bool);
  \check (\force identity) Bool::true: \F(Bool);
  \check (\bind next: Bool -> Bool <- and Bool::true \in
    (\force next) Bool::false): _;

  \normalize (\bind next: Bool -> Bool <- and Bool::false \in (\force next) Bool::false);
  \normalize (\bind next: Bool -> Bool <- and Bool::false \in (\force next) Bool::true);
  \normalize (\bind next: Bool -> Bool <- and Bool::true \in (\force next) Bool::false);
  \normalize (\bind next: Bool -> Bool <- and Bool::true \in (\force next) Bool::true);

  /* Naked arrows in reflection forms denote computation types. */
  \definition andSet: \squash[_](\box[_](and)) =
      \squash[_](\box[_](andExplicit)) :=
    \refl(\squash[_](\box[_](and)));

  \definition identityValueBox: \Box[\F(\U(Bool -> Bool))] :=
    \box[_](\return(identity));
}

\module ProgramCbvSyntaxSugarGeneric(A: \VType, a: A) {
  \definition identity: A -> A := \fun (x: A) => \return(x);
  \definition inferred: \F(A) := identity a;
  \definition inferFunctionType(f: A -> A, x: A): \F(A) := (\force f) x;
}
```

