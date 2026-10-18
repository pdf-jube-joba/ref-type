# declarations / existence

## existence escaping proposition

存在の witness が持つ命題の証明を、任意の別の命題 P の証明として使っている。

```toml case
id = "reject-declarations.existence_escaping_proposition"
scope = "module"
expect = "reject"
name = "EscapingExistentialProposition"
```

```ref
\structure Proof := { P: \Prop, proof: P, };
\definition escape[e: \exists Proof]: \forall(P: \Prop) -> P :=
  \fun(P: \Prop) => \take(r: Proof) => r.proof \by { e };
```

## existence escaping type

存在命題の除去から集合を取り出そうとしている。

```toml case
id = "reject-declarations.existence_escaping_type"
scope = "module"
expect = "reject"
name = "EscapingExistentialType"
```

```ref
\structure Relation := { A: \Set, R: A -> A -> \Prop, };
\definition escape[e: \exists Relation]: \Set :=
  \take(r: Relation) => r.A \by { e };
```

## correspondences

対応する field と law を持つ structure を構築できる。

```toml case
id = "accept-declarations.correspondences"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module BundleSignatures {
/* Program implementations, specifications, and terminating transitions. */
\structure Correspondence := {
  T: \VType,
  program: T,
  specification: T^,
  coherence: program^ = specification,
};

\definition Ready[State, Output: \Set][P: State -> \Prop]: \RunStep[State, Output] -> \Prop :=
  \step-match t: \RunStep[State, Output] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };

\definition Terminates[State, Output: \Set][step: State -> \RunStep[State, Output]][s: State]: \Prop :=
  \forall (P: State -> \Prop) ->
    (\forall (x: State) -> Ready State Output P (step x) -> P x) -> P s;

\structure Machine := {
  State: \VType,
  Output: \VType,
  step: \U(State ~> \F(\RunStep[State, Output])),
  terminates: \forall (s: State^) -> Terminates State^ Output^ step^ s,
  run: \U(State ~> \F(Output)) := \thunk (\cfun (s: State) =>
    \run[State, Output](step, s) \by { terminates s }),
};
}
\module Source(A: \VType) {
  \import \root.BundleSignatures[] \as Signatures;
  \module Implementation {
    \definition helper: A ~> \F(A) := \cfun(x: A) => \return x;
  }
  \import .Implementation[] \as Impl;
  \definition identity: Signatures.Correspondence := Signatures.Correspondence {
    T := \U(A ~> \F(A)), program := \thunk(Impl.helper),
    specification := \fun(x: A^) => x, coherence := \refl(Impl.helper^),
  };
  \definition thunked: Signatures.Correspondence := identity;
}
\module Consumer {
  \import \root.BundleSignatures[] \as Signatures;
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Source[A := Unit] \as S;
  \definition copy: S.identity.T := S.identity.program;
  \definition thunked: S.thunked.T := S.thunked.program;
  \definition reflected: S.identity.T^ := S.identity.specification;
  \macro reflectedType() := S.identity.T^;
  \definition fromMacro: reflectedType!{} := reflected;
  \check S.identity.coherence: copy^ = reflected;
  \definition result: \F(Unit) := (\force copy) Unit::unit;
  \definition reflectedResult: result^ = Unit^::unit := \refl(Unit^::unit);
  \module FirstImplementation {
    \import \root.Source[A := Unit] \as Nested;
    \definition value: Signatures.Correspondence := Nested.identity;
  }
  \module SecondImplementation {
    \import \root.Source[A := Unit] \as Nested;
    \definition value: Signatures.Correspondence := Nested.identity;
  }
  \import .FirstImplementation[] \as First;
  \import .SecondImplementation[] \as Second;
  \definition first: Signatures.Correspondence := First.value;
  \definition second: Signatures.Correspondence := Second.value;
  \check first.coherence: first.program^ = second.specification;
}
```

## existence

存在証明の局所 witness を結論の外に漏らさず利用できる。

```toml case
id = "accept-declarations.existence"
scope = "module"
expect = "accept"
name = "AssociatedExistence"
```

```ref
\inductive Unit: \Set := | unit: Unit;
\structure Relation := { A: \Set, R: A -> A -> \Prop, };
\definition Equality[A: \Set]: Relation := Relation {
  A := A,
  R := \fun(x, y: A) => x = y,
};
\definition existsRelation: \Prop := \exists(r: Relation);
\definition witness: existsRelation := \exact(Equality Unit, Relation);
\definition introduce[r: Relation]: existsRelation := \exact(r, Relation);
\definition keep: existsRelation -> existsRelation :=
  \fun(e: existsRelation) => \take(r: Relation) => \exact(r, Relation) \by { e };
\definition keepBlock: existsRelation -> existsRelation := \block {
  \fun(e: existsRelation) \then
  \takefrom r: Relation \by e \then
  \return \exact(r, Relation)
};

\structure Evidence[P: \Prop] := {
  A: \Set,
  a: A,
  proof: P,
};
\definition evidence: Evidence[Unit::unit = Unit::unit] :=
  Evidence[Unit::unit = Unit::unit] {
    A := Unit, a := Unit::unit, proof := \refl(Unit::unit),
  };
\definition extract[P: \Prop][e: \exists Evidence[P]]: P :=
  \take(r: Evidence[P]) => r.proof \by { e };
\definition extracted: Unit::unit = Unit::unit :=
  extract (Unit::unit = Unit::unit) (\exact(evidence, Evidence[Unit::unit = Unit::unit]));

\structure Nested[P: \Prop] := {
  inner: Evidence[P],
  relation: inner.A -> inner.A -> \Prop,
  reflexive: \forall(x: inner.A) -> relation x x,
};
\definition nested: Nested[Unit::unit = Unit::unit] := Nested[Unit::unit = Unit::unit] {
  inner := evidence,
  relation := \fun(x, y: Unit) => x = y,
  reflexive := \fun(x: Unit) => \refl(x),
};
\definition nestedWitness: \exists Nested[Unit::unit = Unit::unit] :=
  \exact(nested, Nested[Unit::unit = Unit::unit]);
\definition extractNested[P: \Prop][e: \exists Nested[P]]: P := \block {
  \takefrom r: Nested[P] \by e \then
  \return r.inner.proof
};
\definition extractInner[P: \Prop][e: \exists Nested[P]]: \exists Evidence[P] :=
  \take(r: Nested[P]) => \exact(r.inner, Evidence[P]) \by { e };
\definition extractedNested: Unit::unit = Unit::unit :=
  extractNested (Unit::unit = Unit::unit) nestedWitness;

\structure Empty := {};
\definition emptyWitness: \exists Empty := \exact(Empty {}, Empty);
\definition emptyElimination: \forall(P: \Prop) -> P -> \exists Empty -> P :=
  \fun(P: \Prop)(p: P)(e: \exists Empty) => \take(r: Empty) => p \by { e };

\structure Sorted: \Set := { value: Unit, };
\definition sortedWitness: \exists(s: Sorted) :=
  \exact(Sorted { value := Unit::unit, }, Sorted);
\definition sortedElimination: \exists Sorted -> Unit::unit = Unit::unit :=
  \fun(e: \exists Sorted) => \take(s: Sorted) => \refl(Unit::unit) \by { e };
```

