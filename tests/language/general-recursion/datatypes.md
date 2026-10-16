# general-recursion / datatypes

## double negative program inductive

Program 帰納型が二重の負の位置に現れ、strict positivity を満たさない。

```toml case
id = "reject-general-recursion.double-negative-program-inductive"
scope = "module"
expect = "reject"
name = "DoubleNegativeProgramInductive"
```

```ref
\inductive Bad: \VType :=
| bad: \U((\U((Bad ~> \F(Bad))) ~> \F(Bad))) -> Bad
;
```

## duplicate program constructor

Program constructor の名前が重複している。

```toml case
id = "reject-general-recursion.duplicate-program-constructor"
scope = "module"
expect = "reject"
name = "DuplicateProgramConstructor"
```

```ref
\inductive Bad: \VType :=
| same: Bad
| same: Bad
;
```

## non positive program inductive

Program 帰納型が負の位置に現れる。

```toml case
id = "reject-general-recursion.non-positive-program-inductive"
scope = "module"
expect = "reject"
name = "NonPositiveProgramInductive"
```

```ref
\inductive Bad: \VType :=
| bad: \U((Bad ~> \F(Bad))) -> Bad
;
```

## reflected constructor wrong parameter

反映された constructor の型引数が元の帰納型の引数と一致しない。

```toml case
id = "reject-general-recursion.reflected-constructor-wrong-parameter"
scope = "module"
expect = "reject"
name = "WrongReflectedParameter"
```

```ref
\inductive Nat: \VType := | zero: Nat | succ: Nat -> Nat;
\inductive Bit: \VType := | off: Bit | on: Bit;
\inductive Wrap[A: \VType]: \VType := | wrap: A -> Wrap;
\definition bad: Wrap^[Nat^] := Wrap^[Bit^]::wrap Bit^::off;
```

## wrong program constructor result

Program constructor の返り値が宣言対象の帰納型になっていない。

```toml case
id = "reject-general-recursion.wrong-program-constructor-result"
scope = "module"
expect = "reject"
name = "WrongProgramConstructorResult"
```

```ref
\inductive Swap[A, B: \VType]: \VType :=
| wrong: Swap[B, A]
;
```

## compute inductive

Program 帰納型の constructor と case が対応する型を持つ。

```toml case
id = "accept-general-recursion.compute-inductive"
scope = "module"
expect = "accept"
name = "ProgramInductive"
```

```ref
\inductive Bit: \VType :=
| zero: Bit
| one: Bit
;

\definition zero: Bit := Bit::zero;
\definition flip: (Bit ~> \F(Bit)) :=
  (\cfun (x: Bit) => \match (x) \in Bit \with {
    | zero : \return(Bit::one)
    | one : \return(Bit::zero)
    });

\definition one: \F(Bit) := (flip zero);
\normalize (flip zero);
```

## parameterized reflection

Program 帰納型の parameter を Set 側への反映でも保持する。

```toml case
id = "accept-general-recursion.parameterized-reflection"
scope = "module"
expect = "accept"
name = "ParameterizedReflection"
```

```ref
\inductive Unit: \VType :=
| unit: Unit
;

\inductive Box[X: \VType]: \VType :=
| box: X -> Box
;

\definition boxed: Box[Unit] := Box[Unit]::box Unit::unit;
\definition package: \Box[\F(Box[Unit])] :=
  \box[_](\return(boxed));
\infer \squash[_](package);
\normalize \squash[_](package);
\infer Box^[Unit^]::box Unit^::unit;
```

## program case fields

Program case の branch が constructor の field を value として束縛する。

```toml case
id = "accept-general-recursion.program-case-fields"
scope = "module"
expect = "accept"
name = "PairProgram"
parameters = '''A: \VType, a: A, b: A'''
```

```ref
\inductive Pair[X: \VType]: \VType :=
| pair: X -> X -> Pair
;

\definition input: Pair[A] := Pair[A]::pair a b;
\definition swap: Pair[A] ~> \F(Pair[A]) :=
  \cfun (p: Pair[A]) => \match p \in Pair \with {
    | pair left right : \return Pair[A]::pair right left
  };
\normalize (swap input);
```

## recursive program inductive

strict positivity を満たす再帰的 Program 帰納型を定義できる。

```toml case
id = "accept-general-recursion.recursive-program-inductive"
scope = "module"
expect = "accept"
name = "RecursiveProgramInductive"
```

```ref
\inductive Nat: \VType :=
| zero: Nat
| succ: Nat -> Nat
;

\definition one: Nat := Nat::succ Nat::zero;
\definition predecessor: (Nat ~> \F(Nat)) :=
  (\cfun (n: Nat) => \match (n) \in Nat \with {
    | zero : \return(Nat::zero)
    | succ previous : \return(previous)
    });
\normalize (predecessor one);
\definition boxedOne: \Box[\F(Nat)] := \box[_](\return(one));
\normalize \squash[_](boxedOne);
```

## reflected names

反映した Program 帰納型と constructor を生成された名前で参照できる。

```toml case
id = "accept-general-recursion.reflected-names"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source(X: \VType, x: X) {
  \inductive Bool: \VType := | false: Bool | true: Bool;
  \inductive Wrap[A: \VType]: \VType := | wrap: A -> Wrap;

  \definition carrier: \Set := Bool^;
  \definition value: Bool := Bool::true;
  \definition valueSet: Bool^ := value^;
  \definition identity(b: Bool): \F(Bool) := \return b;
  \definition identitySet: Bool^ -> Bool^ := identity^;
  \definition identityAgrees: identitySet valueSet = Bool^::true := \refl(Bool^::true);
  \definition boxedAgrees:
    value^ = \squash[_](\box[_](\return(value))) := \refl(value^);

  \definition parameterCarrier: \Set := X^;
  \definition parameterValue: X^ := x^;
  \definition wrapped: Wrap^[X^] := Wrap^::wrap x^;
  \definition unwrap: Wrap^[X^] -> X^ :=
    \induction (w: Wrap^[X^]) \return X^ \with {
      | wrap: \fun (a: X^) => a
    };
  \definition unwrapAgrees: unwrap wrapped = x^ := \refl(x^);
  \definition eliminate: Bool^ :=
    \match valueSet \in Bool^ \return (\fun (b: Bool^) => Bool^) \with {
      | false : Bool^::true
      | true : Bool^::false
    };
  \definition eliminateAgrees: eliminate = Bool^::false := \refl(Bool^::false);

  \macro truth() := Bool^::true;
  \macro argument() := x^;
  \module Child {
    \definition inherited: Bool^ := value^;
  }
}

\module Consumer {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Source[X := Unit, x := Unit::unit] \as S;
  \import \root.Source[X := Unit, x := Unit::unit] \as Again;
  \import S.Child[] \as Child;
  \use S.truth;
  \use S.argument;

  \inductive Bool: \Set := | other: Bool;
  \definition programValue: S.Bool := S.value;
  \definition reflectedValue: S.Bool^ := S.value^;
  \definition sharedCarrier: Again.Bool^ := reflectedValue;
  \definition childValue: S.Bool^ := Child.inherited;
  \definition fromMacro: S.Bool^ := truth!{};
  \definition fromParameterMacro: Unit^ := argument!{};
  \definition specialized: S.Wrap^[Unit^] := S.wrapped;
  \definition specializationAgrees: S.unwrap specialized = Unit^::unit := \refl(Unit^::unit);

  \definition powerset: \Pow (Unit^) := { u : Unit^ \where u = u };
  \definition logicalArgument: S.Wrap^[\Pow (Unit^)] := S.Wrap^::wrap powerset;
}
```

## reflection conversion

反映と簡約の結果が定義的に等しい。

```toml case
id = "accept-general-recursion.reflection-conversion"
scope = "module"
expect = "accept"
name = "ReflectionConversion"
```

```ref
\inductive Nat: \VType := | zero: Nat | succ: Nat -> Nat;
\inductive Wrap[A: \VType]: \VType := | wrap: A -> Wrap;
\definition identity: (Nat ~> \F(Nat)) := (\cfun (x: Nat) => \return(x));
\definition boxedIdentity: \Box[(Nat ~> \F(Nat))] :=
  \box[_](identity);
\definition boxedZero: \Box[\F(Nat)] := \box[_](\return(Nat::zero));
\definition identitySet: Nat^ -> Nat^ := \squash[_](boxedIdentity);
\definition identityValue: \U((Nat -> Nat)) :=
  \thunk((\cfun (x: Nat) => \return x));
\definition reflectedIdentity: Nat^ := identity^ Nat^::zero;
\definition symbolic: \forall (x: Nat^) -> identitySet x = x := \fun (x: Nat^) => \refl(x);
\definition boxedApplication:
  \squash[_](\boxapp(boxedIdentity, boxedZero)) = Nat^::zero := \refl(Nat^::zero);
\definition mirrorConstructor: Wrap[Nat] := Wrap[Nat]::wrap Nat::zero;
\definition mirrorAgrees:
  mirrorConstructor^ = \squash[_](\box[_](\return(Wrap[Nat]::wrap Nat::zero))) :=
  \refl(mirrorConstructor^);
\definition unwrap: Wrap^[Nat^] -> Nat^ := \induction (x: Wrap^[Nat^]) \return Nat^ \with {
  | wrap: \fun (n: Nat^) => n
};
\definition mirrorRecursor: unwrap mirrorConstructor^ = Nat^::zero := \refl(Nat^::zero);
```

## reflection nested recursive

U と F を通る再帰的な field を反映できる。

```toml case
id = "accept-general-recursion.reflection-nested-recursive"
scope = "module"
expect = "accept"
name = "NestedRecursiveReflection"
```

```ref
\inductive LazyTree: \VType :=
| leaf: LazyTree
| delay: \U(\F(LazyTree)) -> LazyTree
;

\definition delayedLeaf: LazyTree :=
  LazyTree::delay \thunk(\return(LazyTree::leaf));
\definition boxedTree: \Box[\F(LazyTree)] :=
  \box[_](\return(delayedLeaf));

\infer \Box[\F(\U(\F(LazyTree)))];
\normalize \squash[_](boxedTree);
```

## reflection

Program の型と value を対応する Set と要素に反映できる。

```toml case
id = "accept-general-recursion.reflection"
scope = "module"
expect = "accept"
name = "ProgramReflection"
```

```ref
\inductive Bit: \VType :=
| zero: Bit
| one: Bit
;

\definition identity: (Bit ~> \F(Bit)) :=
  (\cfun (x: Bit) => \return(x));
\definition boxedIdentity: \Box[(Bit ~> \F(Bit))] :=
  \box[_](identity);
\definition boxedZero: \Box[\F(Bit)] :=
  \box[_](\return(Bit::zero));

\infer \squash[_](boxedZero);
\normalize \squash[_](boxedZero);
\normalize \squash[_](\boxapp(boxedIdentity, boxedZero));
\infer \induction (x: Bit^) \return Bit^ \with { | zero: Bit^::zero | one: Bit^::one };
```

