# metavariables / holes

## conflicting named constraints

同じ名前の穴に両立しない制約を与えているため、拒否される。

```toml case
id = "reject-metavariables.conflicting_named_constraints"
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

## contextual unsolved goal

局所文脈を持つ inspection hole が残っているため、拒否される。

```toml case
id = "reject-metavariables.contextual_unsolved_goal"
scope = "module"
expect = "reject"
name = "ContextualUnsolvedGoal"
parameters = '''A: \Set(0)'''
```

```ref
/* The reported goal should retain x in its local context. */
\definition pending: A -> A := \fun (x: A) => ?;
```

## metavariable number overflow

名前付き穴の番号が扱える範囲を超えるため、拒否される。

```toml case
id = "reject-metavariables.metavariable_number_overflow"
scope = "module"
expect = "reject"
name = "MetavariableNumberOverflow"
parameters = '''A: \Set(0)'''
```

```ref
\definition pending: A := _4294967296;
```

## named goal captures sibling binder

名前付き穴が別の binder の局所変数を捕捉しようとするため、拒否される。

```toml case
id = "reject-metavariables.named_goal_captures_sibling_binder"
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

## occurs check

穴の解がその穴自身に依存するため、拒否される。

```toml case
id = "reject-metavariables.occurs_check"
scope = "module"
expect = "reject"
name = "MetaOccursCheck"
```

```ref
/* Inferring self-application would require an infinite metavariable type. */
\infer _1 _1;
```

## shared unsolved goal

共有する名前付き穴の制約を解決できないため、拒否される。

```toml case
id = "reject-metavariables.shared_unsolved_goal"
scope = "module"
expect = "reject"
name = "SharedUnsolvedGoal"
```

```ref
/* Repeating the number shares one still-unsolved metavariable. */
\definition pending: \Prop := _6 = _6;
```

## solved inspection argument

解が求まっていても引数位置の inspection hole は確認を要求するため、拒否される。

```toml case
id = "reject-metavariables.solved_inspection_argument"
scope = "module"
expect = "reject"
name = "Inspection"
parameters = '''A: \Set, a: A'''
```

```ref
\definition id: \forall (X: \Set) -> X -> X :=
  \fun (X: \Set) => \fun (x: X) => x;
\definition pending: A := id ? a;
```

## solved inspection program

解が求まっていても Program の inspection hole は確認を要求するため、拒否される。

```toml case
id = "reject-metavariables.solved_inspection_program"
scope = "module"
expect = "reject"
name = "Inspection"
parameters = '''A: \VType, a: A'''
```

```ref
\inductive Box[X: \VType]: \VType := | box: X -> Box;
\definition pending: Box[A] := Box[?]::box a;
```

## solved inspection proof

解が求まっていても証明位置の inspection hole は確認を要求するため、拒否される。

```toml case
id = "reject-metavariables.solved_inspection_proof"
scope = "module"
expect = "reject"
name = "Inspection"
parameters = '''A: \Set, a: A'''
```

```ref
\definition pending: a = a := \refl(?);
```

## two fresh unsolved goals

二つの独立した inspection hole が残っているため、拒否される。

```toml case
id = "reject-metavariables.two_fresh_unsolved_goals"
scope = "module"
expect = "reject"
name = "TwoFreshUnsolvedGoals"
```

```ref
/* Bare question marks are distinct metavariables. */
\definition pending: \Prop := ? = ?;
```

## unsolved goal

inspection hole が残っているため、拒否される。

```toml case
id = "reject-metavariables.unsolved_goal"
scope = "module"
expect = "reject"
name = "UnsolvedGoal"
parameters = '''A: \Set(0)'''
```

```ref
\definition pending: A := ?;
```

## unsolved named goal

名前付き穴を確定できないため、拒否される。

```toml case
id = "reject-metavariables.unsolved_named_goal"
scope = "module"
expect = "reject"
name = "UnsolvedNamedGoal"
parameters = '''A: \Set(0)'''
```

```ref
\definition pending: A := _12;
```

