# inductive / cases

## inductive motive large elimination

帰納型の motive が許可されない大きな sort への除去を要求する。

```toml case
id = "reject-inductive_motive_large_elimination"
scope = "module"
expect = "reject"
name = "LargeElimination"
```

```ref
\inductive Either: \Prop := | left: Either | right: Either;
\definition invalid: Either -> \Prop :=
  \induction (p: Either) \return \Prop \with {
    | left: Either
    | right: Either
  };
```

## inductive motive telescope

帰納型の motive の引数列が帰納型の index と一致しない。

```toml case
id = "reject-inductive_motive_telescope"
scope = "module"
expect = "reject"
name = "MotiveTelescope"
```

```ref
\inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
\inductive Family: \forall (n: Nat) -> \Set := | leaf: \forall (n: Nat) -> Family n;
\definition invalid: Family Nat::zero -> \Prop :=
  \induction (value: Family Nat::zero) \return \Prop \with {
    | leaf: \fun (n: Nat) => n = n
  };
```

## inductives

帰納型の constructor と再帰子の引数が対応している。

```toml case
id = "accept-inductive.inductives"
scope = "module"
expect = "accept"
name = "Ind"
```

```ref
\inductive Unit: \Set :=
| unit: Unit
;

\inductive Bool: \Set :=
| true: Bool
| false: Bool
;

\inductive Nat: \Set :=
| zero: Nat
| succ: Nat -> Nat
;

\definition one: Nat := Nat::succ Nat::zero;
\definition two: Nat := Nat::succ (Nat::succ Nat::zero);
```

## local parameter arguments

帰納型の引数置換が異なる局所変数を区別する。

```toml case
id = "accept-inductive.local_parameter_arguments"
scope = "module"
expect = "accept"
name = "LocalParameterArguments"
parameters = '''A: \Set(0)'''
```

```ref
\inductive Tagged[first: A, second: A]: \Set(0) :=
| tag: Tagged
;

\definition local_constructor:
    \forall (x: A) -> \forall (y: A) -> Tagged[x, y] :=
    \fun (x: A) => \fun (y: A) => Tagged[x, y]::tag;

\definition swapped_constructor:
    \forall (x: A) -> \forall (y: A) -> Tagged[y, x] :=
    \fun (x: A) => \fun (y: A) => Tagged[y, x]::tag;
```

## natural number

自然数の constructor と原始再帰を記述できる。

```toml case
id = "accept-inductive.natural_number"
scope = "module"
expect = "accept"
name = "nat"
```

```ref
\inductive Nat: \Set :=
| zero: Nat
| succ: Nat -> Nat
;

\infer \induction (x: Nat) \return Nat \with { | zero: Nat::zero | succ: \fun (n: _) (ih: _) => Nat::succ ih } ;

\definition copy: Nat -> Nat :=
  \induction (n: Nat) \return Nat \with {
  | succ : \fun (k: Nat) => \fun (ih: Nat) => Nat::succ ih
  | zero : Nat::zero
  };
\normalize copy (Nat::succ Nat::zero);

\definition selfEqual: \forall (n: Nat) -> n = n :=
  \induction (n: Nat) \return n = n \with {
  | succ : \fun (k: Nat) => \fun (ih: k = k) => \refl(Nat::succ k)
  | zero : \refl(Nat::zero)
  };
```

## nested parameters

同じ帰納型を parameter に渡すことと再帰的な field を区別する。

```toml case
id = "accept-inductive.nested_parameters"
scope = "module"
expect = "accept"
name = "NestedParameters"
```

```ref
\inductive Unit: \VType := | unit: Unit;
\inductive Pair[A, B: \VType]: \VType := | pair: A -> B -> Pair;
\definition first: \forall (A, B: \Set) -> Pair^[A, B] -> A :=
  \fun (A, B: \Set) => \induction (p: Pair^[A, B]) \return A \with {
    | pair : \fun (a: A) => \fun (b: B) => a
  };
\definition inner: Pair[Unit, Unit] := Pair[Unit, Unit]::pair Unit::unit Unit::unit;
\definition outer: Pair[Pair[Unit, Unit], Unit] := Pair[Pair[Unit, Unit], Unit]::pair inner Unit::unit;
\definition nestedProjection: first Pair^[Unit^, Unit^] Unit^ outer^ = inner^ := \refl(inner^);
\definition directElimination:
  \induction (p: Pair^[Pair^[Unit^, Unit^], Unit^]) \return Pair^[Unit^, Unit^] \with {
    | pair: \fun (p: Pair^[Unit^, Unit^]) => \fun (u: Unit^) => p
  } outer^ = inner^ := \refl(inner^);
\definition callback: Unit^ -> Pair^[Unit^, Unit^] := \fun (u: Unit^) => inner^;
\definition functionParameter:
  first (Unit^ -> Pair^[Unit^, Unit^]) Unit^
    (Pair^[Unit^ -> Pair^[Unit^, Unit^], Unit^]::pair callback Unit^::unit) Unit^::unit = inner^ := \refl(inner^);

\inductive Count: \Set := | zero: Count | succ: Count -> Count;
\inductive List[A: \Set]: \Set := | nil: List | cons: A -> List -> List;
\definition length: \forall (A: \Set) -> List[A] -> Count :=
  \fun (A: \Set) => \induction (xs: List[A]) \return Count \with {
    | nil: Count::zero
    | cons: \fun (head: A) => \fun (tail: List[A]) => \fun (ih: Count) => Count::succ ih
  };
\definition singleton: List[Unit^] := List[Unit^]::cons Unit^::unit List[Unit^]::nil;
\definition nested: List[List[Unit^]] := List[List[Unit^]]::cons singleton List[List[Unit^]]::nil;
\definition nestedLength: length List[Unit^] nested = Count::succ Count::zero := \refl(Count::succ Count::zero);
\definition directLength:
  \induction (xs: List[List[Unit^]]) \return Count \with {
    | nil: Count::zero
    | cons: \fun (head: List[Unit^]) => \fun (tail: List[List[Unit^]]) => \fun (ih: Count) => Count::succ ih
  }
    nested = Count::succ Count::zero := \refl(Count::succ Count::zero);

/* Genuine recursion under a function domain still receives its hypothesis. */
\inductive Tree[A: \Set]: \Set := | leaf: A -> Tree | node: (Unit^ -> Tree) -> Tree;
\definition depth: \forall (A: \Set) -> Tree[A] -> Count :=
  \fun (A: \Set) => \induction (t: Tree[A]) \return Count \with {
    | leaf: \fun (a: A) => Count::zero
    | node: \fun (children: Unit^ -> Tree[A]) => \fun (ih: Unit^ -> Count) => Count::succ (ih Unit^::unit)
  };
\definition payload: Tree[Unit^] := Tree[Unit^]::leaf Unit^::unit;
\definition nestedTree: Tree[Tree[Unit^]] := Tree[Tree[Unit^]]::node
  (\fun (u: Unit^) => Tree[Tree[Unit^]]::leaf payload);
\definition nestedDepth: depth Tree[Unit^] nestedTree = Count::succ Count::zero := \refl(Count::succ Count::zero);
```

## open motives

局所変数に依存する motive を使って帰納型を除去できる。

```toml case
id = "accept-inductive.open_motives"
scope = "module"
expect = "accept"
name = "OpenMotives"
```

```ref
\inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;

\definition proposition: Nat -> \Prop :=
  \induction (n: Nat) \return \Prop \with {
    | zero: Nat::zero = Nat::zero
    | succ: \fun (n: _) (previous: \Prop) => previous
  };
\definition propositionStep: proposition (Nat::succ Nat::zero) := \refl(Nat::zero);

\definition predicate(Q: \Prop): Nat -> Nat -> \Prop :=
  \induction (n: Nat) \return Nat -> \Prop \with {
    | zero: \fun (m: _) => Q
    | succ: \fun (n: _) (previous: Nat -> \Prop) (m: _) => previous m
  };
\definition captured: predicate (Nat::zero = Nat::zero) (Nat::succ Nat::zero) Nat::zero :=
  \refl(Nat::zero);

\inductive Family[A: \Set]: \forall (x: A) -> \Set :=
  | leaf: \forall (x: A) -> Family x
  | next: \forall (x: A) -> Family x -> Family x;
\definition indexed(A: \Set): \forall (x: A) -> Family[A] x -> \Prop :=
  \induction (x: A) (value: Family[A] x) \return \Prop \with {
    | leaf: \fun (x: _) => x = x
    | next: \fun (x: _) (value: _) (previous: \Prop) => previous
  };
\definition indexedStep: indexed Nat Nat::zero
  (Family[Nat]::next Nat::zero (Family[Nat]::leaf Nat::zero)) := \refl(Nat::zero);
\definition indexedIdentity(A: \Set): \forall (x: A) -> Family[A] x -> Family[A] x :=
  \induction (x: A) (value: Family[A] x) \return Family[A] x \with {
    | leaf: \fun (x: _) => Family[A]::leaf x
    | next: \fun (x: _) (value: _) (previous: _) => Family[A]::next x previous
  };
\definition indexedEquality: indexedIdentity Nat Nat::zero (Family[Nat]::leaf Nat::zero) =
  Family[Nat]::leaf Nat::zero := \refl(Family[Nat]::leaf Nat::zero);

\inductive Tree: \Set := | leaf: Nat -> Tree | node: (Nat -> Tree) -> Tree;
\definition higherOrder: Tree -> Nat -> \Prop :=
  \induction (tree: Tree) \return Nat -> \Prop \with {
    | leaf: \fun (n: _) (m: _) => n = m
    | node: \fun (children: _) (previous: Nat -> Nat -> \Prop) (m: _) => previous m m
  };
\definition higherOrderStep: higherOrder (Tree::node (\fun (n: Nat) => Tree::leaf n)) Nat::zero :=
  \refl(Nat::zero);
```

## parametrized inductive

parameter を持つ帰納型を具体化できる。

```toml case
id = "accept-inductive.parametrized_inductive"
scope = "module"
expect = "accept"
name = "Example"
parameters = '''B: \Set'''
```

```ref
\inductive T[A: \Set]: \Set :=
| w: A -> T
;

\check T[B]::w: B -> T[B];
```

## structure motive

structure を返す motive で帰納型を除去できる。

```toml case
id = "accept-inductive.structure_motive"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module M {
  \inductive Nat: \Set := | zero: Nat | succ: Nat -> Nat;
  \structure Bundle { Carrier: \Set, point: Carrier }
  \module At(n: Nat) {
    \definition point: Nat := n;
  }
  \definition term(n: Nat): Bundle := Bundle { Carrier := Nat, point := At[n := n].point };
  \definition Property(B: Bundle): \Prop := B.point = B.point;
  \definition proof: \forall (n: Nat) -> Property (term n) :=
    \induction (n: Nat) \return Property (term n) \with {
      | zero: \refl(Nat::zero)
      | succ: \fun (n: Nat)(before: _) => \refl(Nat::succ n)
    };
}
```

## unit prec

有限個の constructor の原始再帰子を使える。

```toml case
id = "accept-inductive.unit_prec"
scope = "module"
expect = "accept"
name = "bool"
```

```ref
\inductive Bool: \Set :=
| true : Bool
| false : Bool
;

\infer \induction (x: Bool) \return Bool \with { | true: Bool::true | false: Bool::false };
```

## parameterized prec pair

原始再帰で複数の局所 parameter を正しく置換する。

```toml case
id = "accept-parameterized_prec_pair"
scope = "module"
expect = "accept"
name = "ParameterizedPrecPair"
```

```ref
\inductive Times[A, B: \Set]: \Set :=
| pair: A -> B -> Times
;

\definition first:
  \forall (A, B: \Set) -> Times[A, B] -> A :=
  \fun (A, B: \Set) => \fun (p: Times[A, B]) =>
    \induction (q: Times[A, B]) \return A \with {
      | pair: \fun (a: A) => \fun (b: B) => a
    }
      p;

\definition second:
  \forall (A, B: \Set) -> Times[A, B] -> B :=
  \fun (A, B: \Set) => \fun (p: Times[A, B]) =>
    \induction (q: Times[A, B]) \return B \with {
      | pair: \fun (a: A) => \fun (b: B) => b
    }
      p;
```


## constant motives keep parameters indices and outer variables scoped

parameter と index を持つ帰納型も、外側の変数や定数の型を結果とする match で消去できる。

```toml case
id = "constant_motives_keep_parameters_indices_and_outer_variables_scoped"
scope = "module"
expect = "accept"
name = "Scoped"
parameters = '''A: \Set, a: A'''
```

```ref
\inductive Family[B: \Set]: \forall (x: B) -> \Set :=
  | member: \forall (x: B) -> Family x;
\definition value(x: A) (h: Family[A] x): A :=
  \match h \in Family \return A \with { | member y: y };
\definition same(x: A) (h: Family[A] x): x = x :=
  \match h \in Family \return x = x \with { | member y: \refl(x) };
\definition dependent(x: A) (h: Family[A] x): Family[A] x :=
  \match h \in Family
\return (\fun (y: A) (_: Family[A] y) => Family[A] y)
\with { | member y: Family[A]::member y };
\definition computes: value a (Family[A]::member a) = a := \refl(a);
\definition function(x: A) (h: Family[A] x): A -> A :=
  \match h \in Family \return A -> A \with {
  | member y: \fun (z: A) => z
};
\definition functionComputes:
  function a (Family[A]::member a) a = a := \refl(a);
\inductive Witness[B: \Set]: \forall (x, y: B) -> \Set :=
  | witness: \forall (x, y: B) -> Witness x y;
\definition witnessValue(x, y: A) (h: Witness[A] x y): A :=
  \match h \in Witness \return A \with { | witness y q: y };
\definition witnessComputes:
  witnessValue a a (Witness[A]::witness a a) = a :=
  \refl(a);
\inductive Pair[B, C: \Set]: \Set := | pair: B -> C -> Pair;
\definition first (p: Pair[A, A]): A :=
  \match p \in Pair \return A \with { | pair x y: x };
\definition firstComputes: first (Pair[A, A]::pair a a) = a := \refl(a);
```

## constant return types check every branch

一方の branch だけが、宣言した結果の型と異なる値を返す。

```toml case
id = "constant_return_types_check_every_branch"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A, B: \Set, a: A, b: B'''
```

```ref
\inductive Choice: \Set := | left: Choice | right: Choice;
\definition choose(c: Choice): A :=
  \match c \in Choice \return A \with { | left: a | right: b };
```
