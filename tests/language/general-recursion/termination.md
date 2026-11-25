# Termination certificates

## Certificate for wrong step

The certificate proves a property of a different transition function.

```toml case
id = "certificate-for-wrong-step"
scope = "module"
expect = "reject"
name = "CertificateForWrongStep"
parameters = '''A: \Set, B: \Set,
  first: A -> \RunStep[A, B],
  second: A -> \RunStep[A, B],
  initial: A,
  termination: (\forall (P: A -> \Prop) ->
    (\forall (s: A) ->
      (\step-match t: \RunStep[A, B] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (first s) -> P s) -> P initial)'''
```

```ref
\definition bad: B :=
  \run[A, B](second, initial) \by { termination };
```

## Continue wrong state

The state passed to continue does not have the state-space type.

```toml case
id = "continue-wrong-state"
scope = "module"
expect = "reject"
name = "ContinueWrongState"
parameters = '''A: \VType, B: \VType, b: B'''
```

```ref
\definition bad: \RunStep[A, B] := \continue[A, B](b);
```

## Program run wrong proof

The run proof does not guarantee execution of the specified computation.

```toml case
id = "program-run-wrong-proof"
scope = "module"
expect = "reject"
name = "WrongRunProof"
parameters = '''A: \VType, step: \U((A ~> \F(\RunStep[A, A]))), a: A'''
```

```ref
\eval \run[A, A](step, a) \by { \refl(a^) };
```

## Program runCase checks the transition equality

The supplied reflexivity proof compares the proposed finish result with itself instead of relating it to the reflected step result.

```toml case
id = "program-run-case-transition-equality-mismatch"
scope = "module"
expect = "reject"
name = "WrongRunCaseInvariant"
parameters = '''A: \VType, step: \U((A ~> \F(\RunStep[A, A]))), a: A,
  termination: (\forall (P: A^ -> \Prop) ->
    (\forall (s: A^) ->
      (\step-match t: \RunStep[A^, A^] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step^ s) -> P s) -> P a^)'''
```

```ref
\definition rejected: \F(A) :=
  \runCase[A, A](step, a, \return(\finish[A, A](a)))
    \by { accessibility: termination, equality: \refl(\finish[A^, A^](a^)) };
```

## Set runCase checks the transition equality

The supplied reflexivity proof compares the proposed transition with itself instead of relating it to step initial.

```toml case
id = "set-run-case-transition-equality-mismatch"
scope = "module"
expect = "reject"
name = "RunCaseWrongInvariant"
parameters = '''A: \Set, B: \Set,
  step: A -> \RunStep[A, B],
  initial: A,
  transition: \RunStep[A, B],
  termination: (\forall (P: A -> \Prop) ->
    (\forall (s: A) ->
      (\step-match t: \RunStep[A, B] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step s) -> P s) -> P initial)'''
```

```ref
\definition bad: B :=
  \runCase[A, B](step, initial, transition)
    \by { accessibility: termination, equality: \refl(transition) };
```

## Termination wrong edge

The termination proof's edge does not correspond to the specified state transition.

```toml case
id = "termination-wrong-edge"
scope = "module"
expect = "reject"
name = "WrongEdge"
parameters = '''A: \Set, B: \Set, step: A -> \RunStep[A, B], a, b: A,
  P: A -> \Prop, wrongEdge: step a = \continue[A, B](a)'''
```

```ref
\definition ready: \RunStep[A, B] -> \Prop :=
  \step-match t: \RunStep[A, B] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };
\definition bad [certificate: ready (step a)]: P b :=
  \idelim step a = \continue[A, B](b) \with t: \RunStep[A, B] => ready t
    \by { base: certificate, equality: wrongEdge };
```

## Termination wrong state

The termination proof's state does not belong to the specified state space.

```toml case
id = "termination-wrong-state"
scope = "module"
expect = "reject"
name = "TerminationWrongState"
parameters = '''A: \Set, B: \Set,
  f: A -> \RunStep[A, B],
  b: B'''
```

```ref
\definition bad: \Prop := (\forall (P: A -> \Prop) ->
  (\forall (s: A) ->
    (\step-match t: \RunStep[A, B] \return \Prop \with {
      | \continue next: P next
      | \finish output: \forall (Q: \Prop) -> Q -> Q
    }) (f s) -> P s) -> P b);
```

## Termination wrong step proof

The termination proof does not concern the specified transition.

```toml case
id = "termination-wrong-step-proof"
scope = "module"
expect = "reject"
name = "WrongStepProof"
parameters = '''A: \Set, B: \Set, step: A -> \RunStep[A, B], a: A'''
```

```ref
\definition ready[P: A -> \Prop]: \RunStep[A, B] -> \Prop :=
  \step-match t: \RunStep[A, B] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };
\definition bad: \forall (P: A -> \Prop) ->
  (\forall (s: A) -> ready P (step s) -> P s) -> P a :=
  \fun (P: A -> \Prop) (h: _) => h a (\fun (Q: \Prop) (q: Q) => q);
```

## Wrong initial

The initial state does not match the transition function's input type.

```toml case
id = "wrong-initial"
scope = "module"
expect = "reject"
name = "WrongInitial"
parameters = '''A: \VType, B: \VType,
  f: \U((A ~> \F(\RunStep[A, B]))),
  b: B'''
```

```ref
\definition bad: \F(B) := \run[A, B](f, b) \by { \refl(b^) };
```

## Thunk bodies must match their function types

A return computation is thunked where the declared type requires a function computation.

```toml case
id = "thunk-body-must-match-function-type"
scope = "module"
expect = "reject"
name = "WrongStep"
parameters = '''A: \VType, a: A'''
```

```ref
\definition bad: \U((A ~> \F(A))) := \thunk(\return(a));
```


## Termination proofs through local binders and specialization

The runCase witness proves the same state as the let-bound local variable and remains usable after specialization in another module.

```toml case
id = "program-proofs-follow-local-binders-and-module-instantiation"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Generic(A: \VType, step: \U((A ~> \F(\RunStep[A, A]))),
total: \forall (s: A^) -> (\forall (P: A^ -> \Prop) ->
  (\forall (s: A^) ->
  (\step-match t: \RunStep[A^, A^] \return \Prop \with {
  | \continue next: P next
  | \finish output: \forall (Q: \Prop) -> Q -> Q
}) (step^ s) -> P s) -> P s)) {
  \definition run[x: A]: \F(A) := \run[A, A](step, x) \by { total x };
  \definition runCase[x: A]: \F(A) :=
    (\let y: A := x \in
  \runCase[A, A](step, y, (\force(step)) y) \by { accessibility: total y, equality: \refl(step^ y) });
}
\module Consumer(A: \VType, f: \U((A ~> \F(\RunStep[A, A]))),
p: \forall (s: A^) -> (\forall (P: A^ -> \Prop) ->
  (\forall (s: A^) ->
  (\step-match t: \RunStep[A^, A^] \return \Prop \with {
  | \continue next: P next
  | \finish output: \forall (Q: \Prop) -> Q -> Q
}) (f^ s) -> P s) -> P s), a: A) {
  \import \root.Generic[A := A, step := f, total := p] \as G;
  \definition result: \F(A) := G.runCase a;
  \normalize result;
}
```

## Continue rejects state and result universes that differ

State and Output belong to different universes, so the expression is rejected even with inferred type arguments.

```toml case
id = "continue-rejects-mixed-inferred-universes"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), B: \Set(2), a: A, b: B'''
```

```ref
\definition bad: _ := \continue[_, B](a);
```

## Finish rejects state and result universes that differ

State and Output belong to different universes, so the expression is rejected even with inferred type arguments.

```toml case
id = "finish-rejects-mixed-inferred-universes"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), B: \Set(2), a: A, b: B'''
```

```ref
\definition bad: _ := \finish[A, _](b);
```
