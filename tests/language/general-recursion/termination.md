# general-recursion / termination

## certificate for wrong step

The certificate proves a property of a different transition function.

```toml case
id = "reject-general-recursion.certificate-for-wrong-step"
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

## continue wrong state

The state passed to continue does not have the state-space type.

```toml case
id = "reject-general-recursion.continue-wrong-state"
scope = "module"
expect = "reject"
name = "ContinueWrongState"
parameters = '''A: \VType, B: \VType, b: B'''
```

```ref
\definition bad: \RunStep[A, B] := \continue[A, B](b);
```

## program run wrong proof

The run proof does not guarantee execution of the specified computation.

```toml case
id = "reject-general-recursion.program-run-wrong-proof"
scope = "module"
expect = "reject"
name = "WrongRunProof"
parameters = '''A: \VType, step: \U((A ~> \F(\RunStep[A, A]))), a: A'''
```

```ref
\eval \run[A, A](step, a) \by { \refl(a^) };
```

## program runcase wrong invariant

The Program runCase invariant does not match the transition equality.

```toml case
id = "reject-general-recursion.program-runcase-wrong-invariant"
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

## runcase wrong invariant

The runCase invariant does not establish the required transition equality.

```toml case
id = "reject-general-recursion.runcase-wrong-invariant"
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

## termination wrong edge

The termination proof's edge does not correspond to the specified state transition.

```toml case
id = "reject-general-recursion.termination-wrong-edge"
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

## termination wrong state

The termination proof's state does not belong to the specified state space.

```toml case
id = "reject-general-recursion.termination-wrong-state"
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

## termination wrong step proof

The termination proof does not concern the specified transition.

```toml case
id = "reject-general-recursion.termination-wrong-step-proof"
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

## wrong initial

The initial state does not match the transition function's input type.

```toml case
id = "reject-general-recursion.wrong-initial"
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

## wrong step

The transition function's type does not correspond to the specified state and result types.

```toml case
id = "reject-general-recursion.wrong-step"
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
id = "program_proofs_follow_local_binders_and_module_instantiation"
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

## RunStep universe inference / 1

State and Output belong to different universes, so the expression is rejected even with inferred type arguments.

```toml case
id = "mixed-inferred-step-0"
scope = "module"
expect = "reject"
name = "Mixed"
parameters = '''A: \Set(0), B: \Set(2), a: A, b: B'''
```

```ref
\definition bad: _ := \continue[_, B](a);
```

## RunStep universe inference / 2

State and Output belong to different universes, so the expression is rejected even with inferred type arguments.

```toml case
id = "mixed-inferred-step-1"
scope = "module"
expect = "reject"
name = "Mixed"
parameters = '''A: \Set(0), B: \Set(2), a: A, b: B'''
```

```ref
\definition bad: _ := \finish[A, _](b);
```
