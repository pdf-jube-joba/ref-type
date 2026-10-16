# system / refinement

## powerset requires set

冪集合の対象が集合ではない。

```toml case
id = "reject-system.powerset_requires_set"
scope = "module"
expect = "reject"
name = "PowerSetRequiresSet"
parameters = '''P: \Prop,'''
```

```ref
\definition bad: \Set(0) := \Pow (P);
```

## predicate wrong element

述語に渡した要素が指定された ambient set に属さない。

```toml case
id = "reject-system.predicate_wrong_element"
scope = "module"
expect = "reject"
name = "PredicateWrongElement"
parameters = '''A, B: \Set(0),
    subsetOfA: \Pow (A),
    b: B,'''
```

```ref
\definition bad: \Prop := \In[A] (subsetOfA) (b);
```

## subset elim requires refined element

部分集合の除去に refinement の要素ではない値を渡す。

```toml case
id = "reject-system.subset_elim_requires_refined_element"
scope = "module"
expect = "reject"
name = "SubsetElimRequiresRefinedElement"
parameters = '''A: \Set(0),
    P: A -> \Prop,
    a: A,'''
```

```ref
\definition PSet: \Pow (A) := { x : A \where P x };
\definition bad: \In[A] (PSet) (a) := \bysub(A, PSet, a);
```

## subset intro wrong proof

部分集合の導入に渡した証明が witness の所属を示さない。

```toml case
id = "reject-system.subset_intro_wrong_proof"
scope = "module"
expect = "reject"
name = "SubsetIntroWrongProof"
parameters = '''A: \Set(0),
    P, Q: A -> \Prop,
    a: A,
    qa: Q a,'''
```

```ref
\definition PSet: \Pow (A) := { x : A \where P x };
\definition PA: \Set(0) := \Cast[A] (PSet);
\definition bad: PA := \into[A](a, PSet) \by { qa };
```

## subset requires proposition

部分集合の条件が命題ではない。

```toml case
id = "reject-system.subset_requires_proposition"
scope = "module"
expect = "reject"
name = "SubsetRequiresProposition"
parameters = '''A: \Set(0),'''
```

```ref
\definition bad: \Pow (A) := { x : A \where A };
```

## type lift wrong carrier

refinement が指定された ambient set の部分集合ではない。

```toml case
id = "reject-system.type_lift_wrong_carrier"
scope = "module"
expect = "reject"
name = "TypeLiftWrongCarrier"
parameters = '''A, B: \Set(0),
    subsetOfB: \Pow (B),'''
```

```ref
\definition bad: \Set(0) := \Cast[A] (subsetOfB);
```

## subset intro

部分集合の witness と所属証明を組み合わせられる。

```toml case
id = "accept-subset_intro"
scope = "module"
expect = "accept"
name = "SubsetIntro"
parameters = '''A: \Set(0),
    P: A -> \Prop,
    a, b: A,
    pa: P a,
    ab: a = b,'''
```

```ref
/* A subset and its corresponding refinement type may be named normally. */
\definition XSet: \Pow (A) := { x : A \where P x };
\definition X: \Set(0) := \Cast[A] (XSet);

/* Membership is checked at this construction boundary. */
\definition xa: X := \into[A](a, XSet) \by { pa };

/* Equality elimination transports the assumed proof `pa: P a` to `P b`. */
\definition pb: P b :=
    \idelim a = b \with x: A => P x \by { base: pa, equality: ab };
\definition xb: X := \into[A](b, XSet) \by { pb };

/* Refinement values weaken implicitly to their carrier. */
\definition forget: \forall (x: X) -> A :=
    \fun (x: X) => x;
\definition underlying_a: A := xa;
\definition underlying_b: A := xb;

/* SubsetIntro erases when observed through the carrier. */
\definition property_a: P a :=
    \bysub(A, { x : A \where P x }, xa);
\definition property_b: P b :=
    \bysub(A, { x : A \where P x }, xb);

/* Reusing a checked value does not repeat its introduction proof. */
\definition reuse: \forall (x: X) -> X :=
    \fun (x: X) => x;
\definition reuse_a: X := reuse xa;
\definition reuse_b: X := reuse xb;

/* Both checked values may pass through ordinary higher-order code. */
\definition apply_both: (\forall (x: X) -> \forall (y: X) -> A) -> A :=
    \fun (f: \forall (x: X) -> \forall (y: X) -> A) => f xa xb;

/* Weakening also exposes a carrier function in function position. */
\definition Endo: \Set(0) := A -> A;
\definition GoodEndoSet: \Pow (Endo) :=
    { f : Endo \where f = f };
\definition GoodEndo: \Set(0) :=
    \Cast[Endo] (GoodEndoSet);
\definition identity: Endo := \fun (x: A) => x;
\definition checked_identity: GoodEndo :=
    \into[Endo](identity, GoodEndoSet) \by { \refl(identity) };
\definition applied: A := checked_identity a;

/* Equality forgets distinct refinements when they share a carrier. */
\definition ReflexiveSet: \Pow (A) :=
    { x : A \where x = x };
\definition Reflexive: \Set(0) :=
    \Cast[A] (ReflexiveSet);
\definition reflexive_a: Reflexive :=
    \into[A](a, ReflexiveSet) \by { \refl(a) };
\definition same_underlying_value: xa = reflexive_a :=
    \refl(xa);
```

## id elim local subset

局所的な部分集合を motive と binder の下でも保持する。

```toml case
id = "accept-system.id_elim_local_subset"
scope = "module"
expect = "accept"
name = "LocalSubset"
parameters = '''A: \Set'''
```

```ref
\definition transport(Left: \Pow (A)) (Right: \Pow (A))
    (x: \Cast[\Pow (A)] ({ T : \Pow (A) \where T = Left -> T = Right }))
    (y: \Cast[\Pow (A)] ({ T : \Pow (A) \where T = Left -> T = Right }))
    (e: x = y):
    \forall (h: \In[\Pow (A)] ({ T : \Pow (A) \where T = Left -> T = Right }) (y)) ->
        x = \into[\Pow (A)](y, { T : \Pow (A) \where T = Left -> T = Right }) \by { h } :=
    \idelim x = y \with z: \Pow (A) =>
        \forall (h: \In[\Pow (A)] ({ T : \Pow (A) \where T = Left -> T = Right }) (z)) ->
            x = \into[\Pow (A)](z, { T : \Pow (A) \where T = Left -> T = Right }) \by { h }
    \by { base: (\fun (h: \In[\Pow (A)] ({ T : \Pow (A) \where T = Left -> T = Right }) (x)) => \refl(x)), equality: e };

\macro subsetEquality($X) :=
    (\fun (law: \forall (x, y: \Cast[\Pow (A)] ($X)) -> x = y -> y = x) => law)
    (\fun (x, y: \Cast[\Pow (A)] ($X)) => \fun (e: x = y) =>
        (\idelim x = y \with z: \Pow (A) =>
            \forall (h: \In[\Pow (A)] ($X) (z)) ->
                \into[\Pow (A)](z, $X) \by { h } = x
        \by { base: (\fun (h: \In[\Pow (A)] ($X) (x)) => \refl(x)), equality: e })
        (\bysub(\Pow (A), $X, y)));

/* The macro repeats a type containing local binders in grouped annotations. */
\definition reverse(Left, Right: \Pow (A))
    (x, y: \Cast[\Pow (A)] ({ T : \Pow (A) \where T = Left -> T = Right }))
    (e: x = y): y = x :=
    subsetEquality!{ { { T : \Pow (A) \where T = Left -> T = Right } } } x y e;
```

## inductive elimination through refinement

refinement を通して帰納型の要素を除去できる。

```toml case
id = "accept-system.inductive_elimination_through_refinement"
scope = "module"
expect = "accept"
name = "RefinedNaturalElimination"
```

```ref
\inductive Nat: \Set :=
| zero: Nat
| succ: Nat -> Nat
;

\definition Reflexive: \Pow (Nat) :=
  { n : Nat \where n = n };

\definition RefinedNat: \Set :=
  \Cast[Nat] (Reflexive);

\definition eliminate: RefinedNat -> Nat :=
  \fun (n: RefinedNat) =>
    \match n \in Nat \return (\fun (k: Nat) => Nat) \with {
    | zero : Nat::zero
    | succ k : Nat::succ k
    };

\normalize eliminate (Nat::succ Nat::zero);
```

## nested subset applications

入れ子の refinement と application が型を保つ。

```toml case
id = "accept-system.nested_subset_applications"
scope = "module"
expect = "accept"
name = "NestedSubsetApplications"
parameters = '''A: \Set(0),
    P: A -> \Prop,
    a: A,
    pa: P a,
    Family: A -> \Set(0),
    indexed: Family a,'''
```

```ref
\definition ASubset: \Pow (A) := { x : A \where P x };
\definition RefinedA: \Set(0) := \Cast[A] (ASubset);
\definition refined_a: RefinedA :=
    \into[A](a, ASubset) \by { pa };

\definition Endo: \Set(0) := A -> A;
\definition GoodEndoSet: \Pow (Endo) :=
    { f : Endo \where f = f };
\definition GoodEndo: \Set(0) := \Cast[Endo] (GoodEndoSet);
\definition identity: Endo := \fun (x: A) => x;
\definition checked_identity: GoodEndo :=
    \into[Endo](identity, GoodEndoSet) \by { \refl(identity) };

/* The function and argument are both literal SubsetIntro expressions. */
\definition intro_in_both_positions: A :=
    (\into[Endo](identity, GoodEndoSet) \by { \refl(identity) })
    (\into[A](a, ASubset) \by { pa });

/* The same path through named checked values. */
\definition named_in_both_positions: A := checked_identity refined_a;
\definition nested_higher_order: A :=
    (\fun (f: Endo) => \fun (x: A) => f x) checked_identity refined_a;

/* Erased conversion also acts inside a dependent type argument. */
\definition indexed_by_intro:
    Family (\into[A](a, ASubset) \by { pa }) := indexed;
\definition indexed_by_named_intro: Family refined_a := indexed;
```

## refinement eliminators

refinement の witness と所属証明を対応する型で取り出せる。

```toml case
id = "accept-system.refinement_eliminators"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Refinement {
  \definition Checked(A: \Set): \Set := \Cast[A] ({ x: A \where x = x });
  \definition refine(A: \Set)(x: A): Checked A :=
    \into[A](x, { y: A \where y = y }) \by { \refl(x) };
}

\module RefinedMembership(A: \Set, P: A -> \Prop, S: \Pow A) {
  \import \root.Refinement[] \as R;
  \definition bare: \Pow A := { x: A \where P x };
  \definition refined: R.Checked (\Pow A) := R.refine (\Pow A) bare;
  \definition nested: R.Checked (R.Checked (\Pow A)) :=
    R.refine (R.Checked (\Pow A)) refined;

  \definition direct(x: A): P x -> \In[A] nested x := \fun (h: _) => h;
  \definition reverse(x: A): \In[A] nested x -> P x := \fun (h: _) => h;
  \definition annotated(x: A): P x -> \In[A] (nested \of \Pow A) x :=
    \fun (h: _) => h;
  \definition opaque(x: A): \In[A] S x -> \In[A] (R.refine (\Pow A) S) x :=
    \fun (h: _) => h;

  \definition retain: \forall (x: \Cast[A] bare) -> \In[A] nested x :=
    \fun (x: _) => \bysub(A, bare, x);
  \definition make(x: A): P x -> \exists \Cast[A] nested := \block {
    \fun (h: P x) \then
    \return \exact(\into[A](x, nested) \by { h }, \Cast[A] nested)
  };
}

\module RefinedSteps {
  \import \root.Refinement[] \as R;
  \inductive Unit: \Set := | unit: Unit;
  \definition Step: \Set := \RunStep[Unit, Unit];
  \definition select: Step -> Unit :=
    \step-match t: \RunStep[Unit, Unit] \return Unit \with {
      | \continue next: next
      | \finish output: output
    };
  \definition next: R.Checked Step := R.refine Step (\continue[Unit, Unit](Unit::unit));
  \definition done: R.Checked Step := R.refine Step (\finish[Unit, Unit](Unit::unit));
  \definition selectNext: select next = Unit::unit := \refl(Unit::unit);
  \definition selectDone: select done = Unit::unit := \refl(Unit::unit);

  \definition step(s: Unit): Step := done;
  \definition Terminates(s: Unit): \Prop :=
    \forall (P: Unit -> \Prop) ->
      (\forall (x: Unit) ->
        (\step-match t: \RunStep[Unit, Unit] \return \Prop \with {
          | \continue next: P next
          | \finish output: \forall (Q: \Prop) -> Q -> Q
        }) (step x) -> P x) -> P s;
  \definition terminates(s: Unit): Terminates s :=
    \fun (P: _) (h: _) => h s (\fun (Q: \Prop)(q: Q) => q);
  \definition run: \run[Unit, Unit](step, Unit::unit) \by { terminates Unit::unit } = Unit::unit :=
    \refl(Unit::unit);
}

\module RefinedBoxes {
  \import \root.Refinement[] \as R;
  \inductive Bit: \VType := | zero: Bit | one: Bit;
  \definition identity: \Box[Bit ~> \F(Bit)] :=
    \box[_](\cfun (x: Bit) => \return x);
  \definition input: \Box[\F(Bit)] := \box[_](\return Bit::one);
  \definition checkedIdentity: R.Checked (\Box[Bit ~> \F(Bit)]) :=
    R.refine (\Box[Bit ~> \F(Bit)]) identity;
  \definition checkedInput: R.Checked (\Box[\F(Bit)]) := R.refine (\Box[\F(Bit)]) input;
  \definition squash: \squash[\F(Bit)](checkedInput) = Bit^::one := \refl(Bit^::one);
  \definition apply: \squash[_](\boxapp(
    checkedIdentity \of \Box[Bit ~> \F(Bit)], checkedInput)) = Bit^::one :=
    \refl(Bit^::one);
}
```

## subset and equality

部分集合への所属と ambient set の等号を組み合わせられる。

```toml case
id = "accept-system.subset_and_equality"
scope = "module"
expect = "accept"
name = "SubsetAndEquality"
parameters = '''A: \Set(0),
    P, Q: A -> \Prop,
    a: A,
    pa: P a,
    qa: Q a,'''
```

```ref
\definition PSet: \Pow (A) := { x : A \where P x };
\definition QSet: \Pow (A) := { x : A \where Q x };
\definition PA: \Set(0) := \Cast[A] (PSet);
\definition QA: \Set(0) := \Cast[A] (QSet);

\definition inP: PA := \into[A](a, PSet) \by { pa };
\definition inQ: QA := \into[A](a, QSet) \by { qa };
\definition weakenedP: A := inP;
\definition membershipP: \In[A] (PSet) (inP) :=
    \bysub(A, PSet, inP);

/* Distinct refinements over the same carrier admit an equality type. */
\definition same_carrier: inP = inQ := \refl(inP);
```

