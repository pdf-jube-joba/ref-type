# system / sorts

## application wrong argument

application の引数が関数の domain の型を持たない。

```toml case
id = "reject-system.application_wrong_argument"
scope = "module"
expect = "reject"
name = "ApplicationWrongArgument"
parameters = '''A, B: \Set(0),
    f: A -> A,
    b: B,'''
```

```ref
\definition bad: A := f b;
```

## non cumulative

異なる universe level の集合を暗黙に同一視している。

```toml case
id = "reject-system.non_cumulative"
scope = "module"
expect = "reject"
name = "NonCumulative"
parameters = '''A: \Set(0)'''
```

```ref
\definition lifted_type: \Set(1) := A;
```

## product invalid sort relation

積の domain と codomain が許可された sort 関係を満たさない。

```toml case
id = "reject-system.product_invalid_sort_relation"
scope = "module"
expect = "reject"
name = "ProductInvalidSortRelation"
parameters = '''P: \Prop,
    A: \Set(0)'''
```

```ref
\definition bad: \Set(0) := \forall (p: P) -> A;
```

## pair cumulative

pair の成分を宣言された universe の条件で組み合わせられる。

```toml case
id = "accept-pair_cumulative"
scope = "module"
expect = "accept"
name = "PairCumulative"
```

```ref
\inductive Times[A, B: \Set]: \Set :=
| pairConstructor: A -> B -> Times
;

\definition pair:
  \forall (A, B: \Set) -> A -> B -> Times[A, B] :=
  \fun (A, B: \Set) => \fun (a: A) => \fun (b: B) =>
    Times[A, B]::pairConstructor a b;
```

## axioms

公開された公理を対応する型を持つ証明 constructor として使える。

```toml case
id = "accept-system.axioms"
scope = "module"
expect = "accept"
name = "Axioms"
parameters = '''X, Y: \Set,
    A, B: \Pow (X),
    ab: \forall (x: X) -> \In[X] (A) (x) -> \In[X] (B) (x),
    ba: \forall (x: X) -> \In[X] (B) (x) -> \In[X] (A) (x),
    f, g: X -> Y,
    pointwise: \forall (x: X) -> f x = g x,
    Family: X -> \Set,
    inhabited: \forall (x: X) -> \exists (Family x),'''
```

```ref
\definition subset_extensionality: A = B :=
    \axiom:setext(A, B, ab, ba);

\definition function_extensionality: f = g :=
    \axiom:funext(f, g, pointwise);

\definition indefinite_choice: \exists (\forall (x: X) -> Family x) :=
    \axiom:classicalIndefiniteChoice(X, Family, inhabited);
```

## nested functions

入れ子の関数で外側と内側の binder を区別する。

```toml case
id = "accept-system.nested_functions"
scope = "module"
expect = "accept"
name = "NestedFunctions"
parameters = '''A, B, C: \Set(0),
    a: A,
    f: A -> B,
    g: B -> C,
    Family: A -> \Set(0),
    dependent: \forall (x: A) -> Family x,'''
```

```ref
\definition compose: (B -> C) -> (A -> B) -> A -> C :=
    \fun (outer: B -> C) =>
    \fun (inner: A -> B) =>
    \fun (x: A) => outer (inner x);

\definition composed_at_a: C := compose g f a;
\definition nested_application: C :=
    (\fun (identity: C -> C) => identity (g (f a))) (\fun (x: C) => x);

\definition dependent_identity:
    (\forall (h: \forall (x: A) -> Family x) -> \forall (x: A) -> Family x) :=
    \fun (h: \forall (x: A) -> Family x) => \fun (x: A) => h x;
\definition dependent_at_a: Family a :=
    dependent_identity dependent a;

\definition higher_order_check:
    (\forall (h: A -> B) -> \forall (k: B -> C) -> C) :=
    \fun (h: A -> B) => \fun (k: B -> C) => k (h a);
```

## pure type system

許可された sort 関係で型と積を形成できる。

```toml case
id = "accept-system.pure_type_system"
scope = "module"
expect = "accept"
name = "PureTypeSystem"
parameters = '''A: \Set(0),
    B: \Set(0),
    a: A,
    b: B,
    P: \Prop,
    p: P,'''
```

```ref
\definition identity: \forall (X: \Set(0)) -> \forall (x: X) -> X :=
    \fun (X: \Set(0)) => \fun (x: X) => x;
\definition constant: \forall (x: A) -> \forall (y: B) -> A :=
    \fun (x: A) => \fun (y: B) => x;
\definition applied: A := identity A a;

/* Products ending in Prop remain propositions. */
\definition implication: \Prop := P -> P;
\definition proof_identity: P -> P := \fun (q: P) => q;
\definition proof_application: P := proof_identity p;

/* The declared universe matches the syntax index. */
\definition same_level_type: \Set(0) := A;
```

## record induction

record を帰納的に分解して対応する motive の証明を構築できる。

```toml case
id = "accept-system.record_induction"
scope = "module"
expect = "accept"
name = "Records"
```

```ref
\structure Pair[A, B: \Set]: \Set := {
  left: A,
  right: B,
};
\definition eta: \forall (A, B: \Set)(p: Pair[A, B]) -> Pair[A, B]::# (p.left) (p.right) = p :=
  \fun (A, B: \Set) => \induction (p: Pair[A, B]) \return Pair[A, B]::# (p.left) (p.right) = p \with {
    | # : \fun (left: A)(right: B) => \refl(Pair[A, B]::# left right)
  };
```

