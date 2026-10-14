# general-recursion / termination

## certificate for wrong step

証明書が別の遷移関数についての証明になっているため、拒否される。

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

continue に渡した状態が状態空間の型を持たないため、拒否される。

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

run の証明が指定された computation の実行を保証しないため、拒否される。

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

Program runCase の不変条件が遷移等式と一致しないため、拒否される。

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

runCase の不変条件が要求される遷移等式を示していないため、拒否される。

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

停止証明の辺が指定された状態遷移に対応していないため、拒否される。

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
\definition bad (certificate: ready (step a)): P b :=
  \idelim step a = \continue[A, B](b) \with t: \RunStep[A, B] => ready t
    \by { base: certificate, equality: wrongEdge };
```

## termination wrong state

停止証明の状態が指定された状態空間に属さないため、拒否される。

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

停止証明が指定された遷移についての証明になっていないため、拒否される。

```toml case
id = "reject-general-recursion.termination-wrong-step-proof"
scope = "module"
expect = "reject"
name = "WrongStepProof"
parameters = '''A: \Set, B: \Set, step: A -> \RunStep[A, B], a: A'''
```

```ref
\definition ready(P: A -> \Prop): \RunStep[A, B] -> \Prop :=
  \step-match t: \RunStep[A, B] \return \Prop \with {
    | \continue s: P s
    | \finish result: \forall (Q: \Prop) -> Q -> Q
  };
\definition bad: \forall (P: A -> \Prop) ->
  (\forall (s: A) -> ready P (step s) -> P s) -> P a :=
  \fun (P: A -> \Prop) (h: _) => h a (\fun (Q: \Prop) (q: Q) => q);
```

## wrong initial

初期状態が遷移関数の入力型と一致しないため、拒否される。

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

遷移関数の型が指定された状態型と結果型に対応していないため、拒否される。

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

