# Inference and inspection holes

## Conflicting named constraints

Holes with the same name receive incompatible constraints.

```toml case
id = "conflicting-named-constraints"
scope = "module"
expect = "reject"
name = "ConflictingNamedConstraints"
parameters = '''A: \Set(0),
  B: \Set(0),
  a: A,
  b: B'''
```

```ref
\definition chooseLeft:
  \forall (X: \Set(0)) -> X -> X -> X :=
  \fun (X: \Set(0)) => \fun (left: X) => \fun (right: X) => left;

/* _2 would have to be both A and B. */
\definition impossible: A := chooseLeft _2 a b;
```

## Contextual unsolved goal

An inspection hole with a local context remains.

```toml case
id = "contextual-unsolved-goal"
scope = "module"
expect = "reject"
name = "ContextualUnsolvedGoal"
parameters = '''A: \Set(0)'''
```

```ref
\definition pending: A -> A := \fun (x: A) => ?;
```

## Named goal captures sibling binder

A named hole attempts to capture a local variable from a different binder.

```toml case
id = "named-goal-captures-sibling-binder"
scope = "module"
expect = "reject"
name = "NamedGoalCapturesSiblingBinder"
parameters = '''A: \Set(0),
  P: \Prop'''
```

```ref
/* The two _9 occurrences share only the scope outside x and y. */
\definition impossible:
  ((\forall (x: A) -> x = x) -> (\forall (y: A) -> y = y) -> P) -> P :=
  \fun (consume: (\forall (x: A) -> x = x) -> (\forall (y: A) -> y = y) -> P) =>
    consume
      (\fun (x: A) => \refl(_9))
      (\fun (y: A) => \refl(_9));
```

## Occurs check

A hole's solution depends on the hole itself.

```toml case
id = "occurs-check"
scope = "module"
expect = "reject"
name = "MetaOccursCheck"
```

```ref
/* Inferring self-application would require an infinite metavariable type. */
\infer _1 _1;
```

## Shared unsolved goal

Constraints on a shared named hole cannot be solved.

```toml case
id = "shared-unsolved-goal"
scope = "module"
expect = "reject"
name = "SharedUnsolvedGoal"
```

```ref
/* Repeating the number shares one still-unsolved metavariable. */
\definition pending: \Prop := _6 = _6;
```

## Solved inspection argument

An inspection hole in argument position requires inspection even when solved.

```toml case
id = "solved-inspection-argument"
scope = "module"
expect = "reject"
parameters = '''A: \Set, a: A'''
```

```ref
\definition id: \forall (X: \Set) -> X -> X :=
  \fun (X: \Set) => \fun (x: X) => x;
\definition pending: A := id ? a;
```

## Solved inspection program

A Program inspection hole requires inspection even when solved.

```toml case
id = "solved-inspection-program"
scope = "module"
expect = "reject"
parameters = '''A: \VType, a: A'''
```

```ref
\inductive Box[X: \VType]: \VType := | box: X -> Box;
\definition pending: Box[A] := Box[?]::box a;
```

## Solved inspection proof

An inspection hole in proof position requires inspection even when solved.

```toml case
id = "solved-inspection-proof"
scope = "module"
expect = "reject"
parameters = '''A: \Set, a: A'''
```

```ref
\definition pending: a = a := \refl(?);
```

## Two fresh unsolved goals

Two independent inspection holes remain.

```toml case
id = "two-fresh-unsolved-goals"
scope = "module"
expect = "reject"
name = "TwoFreshUnsolvedGoals"
```

```ref
/* Bare question marks are distinct metavariables. */
\definition pending: \Prop := ? = ?;
```

## Unsolved goal

An inspection hole remains.

```toml case
id = "unsolved-goal"
scope = "module"
expect = "reject"
name = "UnsolvedGoal"
parameters = '''A: \Set(0)'''
```

```ref
\definition pending: A := ?;
```

## Unsolved named goal

A named hole cannot be resolved.

```toml case
id = "unsolved-named-goal"
scope = "module"
expect = "reject"
name = "UnsolvedNamedGoal"
parameters = '''A: \Set(0)'''
```

```ref
\definition pending: A := _12;
```

