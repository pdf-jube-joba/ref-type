# metavariables / inference

## ambiguous implicit value

There are insufficient constraints to determine the implicit value uniquely.

```toml case
id = "reject-metavariables.ambiguous_implicit_value"
scope = "module"
expect = "reject"
name = "AmbiguousImplicitValue"
parameters = '''A: \Set(0), candidate: A'''
```

```ref
/* Metavariables are not solved by searching the local context. */
\definition pending: A := _;
```

## ambiguous inductive argument

There are insufficient constraints to determine the inductive argument uniquely.

```toml case
id = "reject-metavariables.ambiguous_inductive_argument"
scope = "module"
expect = "reject"
name = "AmbiguousInductiveArgument"
```

```ref
\inductive Box[X: \Set(0)]: \Set(0) :=
  | box: X -> Box
;

/* No field or expected type determines X. */
\infer Box[_]::box;
```

## ambiguous module parameter

A module parameter's type cannot be determined.

```toml case
id = "reject-metavariables.ambiguous_module_parameter"
scope = "module"
expect = "reject"
name = "AmbiguousModuleParameter"
parameters = '''A: _'''
```

```ref

```

## ambiguous program value

There are insufficient constraints to determine the Program value's type uniquely.

```toml case
id = "reject-metavariables.ambiguous_program_value"
scope = "module"
expect = "reject"
name = "AmbiguousProgramValue"
parameters = '''A: \VType'''
```

```ref
\definition pending: A := _;
```

## application inference

Holes can be inferred from an application's expected type and arguments.

```toml case
id = "accept-metavariables.application_inference"
scope = "module"
expect = "accept"
name = "MetaApplication"
parameters = '''A: \Set(0), a: A'''
```

```ref
\definition id:
  \forall (X: \Set(0)) -> X -> X :=
  \fun (X: \Set(0)) => \fun (x: X) => x;

\definition chooseLeft:
  \forall (X: \Set(0)) -> X -> X -> X :=
  \fun (X: \Set(0)) => \fun (left: X) => \fun (right: X) => left;

/* Inference variables can be solved by a later argument. */
\definition implicit: A := id _ a;
\definition namedImplicit: A := id _2 a;

/* Repeated _N occurrences in one declaration denote the same meta. */
\definition sharedNamedImplicit: A :=
  chooseLeft _7 (id _7 a) a;

\infer id _ a;
\eval id _ a;
\normalize id _ a;
```

## bidirectional inference

Constraints from expected types to terms and from terms to types can be combined.

```toml case
id = "accept-metavariables.bidirectional_inference"
scope = "module"
expect = "accept"
name = "MetaBidirectional"
parameters = '''A: \Set(0), a: A'''
```

```ref
\definition identity: A -> A := \fun (x: _) => x;
\definition nestedIdentity: A -> A :=
  \fun (x: _) => (\fun (X: \Set(0)) => \fun (value: X) => value) _ x;

/* The checked term determines the expected-type hole. */
\check a: _;

/* The body determines a hole used as the declared type. */
\definition inferredDeclarationType: _ := a;
```

## contextual inference

A hole's solution is well-typed in its local context.

```toml case
id = "accept-metavariables.contextual_inference"
scope = "module"
expect = "accept"
name = "MetaContextual"
```

```ref
\definition apply:
  \forall (A: \Set(0)) -> A -> A :=
  \fun (A: \Set(0)) => \fun (x: A) =>
    (\fun (X: \Set(0)) => \fun (value: X) => value) _ x;

\definition applyNamed:
  \forall (A: \Set(0)) -> A -> A :=
  \fun (A: \Set(0)) => \fun (x: A) =>
    (\fun (X: \Set(0)) => \fun (value: X) => value) _4 x;

/* A named meta shared by sibling lambdas may only use their common scope. */
\definition siblingLambdas:
  \forall (A: \Set(0)) -> ((A -> A) -> (A -> A) -> A) -> A :=
  \fun (A: \Set(0)) =>
    \fun (consume: (A -> A) -> (A -> A) -> A) =>
      consume
        (\fun (x: A) => (\fun (X: \Set(0)) => \fun (value: X) => value) _9 x)
        (\fun (y: A) => (\fun (X: \Set(0)) => \fun (value: X) => value) _9 y);
```

## declaration scopes

Hole-sharing scopes follow declaration boundaries.

```toml case
id = "accept-metavariables.declaration_scopes"
scope = "module"
expect = "accept"
name = "MetaDeclarationScopes"
parameters = '''A: \Set(0), a: A'''
```

```ref
\definition id:
  \forall (X: \Set(0)) -> X -> X :=
  \fun (X: \Set(0)) => \fun (x: X) => x;

/* Named metavariables are scoped to one declaration. */
\definition first: A := id _1 a;
\definition second: A := id _1 a;
\definition third: A := id _1 a;
```

## equality inference

The carrier and type arguments can be inferred from both sides of an equality.

```toml case
id = "accept-metavariables.equality_inference"
scope = "module"
expect = "accept"
name = "MetaEquality"
parameters = '''A: \Set(0), a: A'''
```

```ref
\definition implicitReflexivity: a = a := \refl(_);
\definition namedImplicitReflexivity: a = a := \refl(_5);
```

## id elim inferred carrier

The carrier for equality elimination can be inferred from both sides of the equality.

```toml case
id = "accept-metavariables.id_elim_inferred_carrier"
scope = "module"
expect = "accept"
name = "Example"
parameters = '''A: \Set(1), a, b, c: A, ab: a = b, bc: b = c'''
```

```ref
\definition transitive: a = c :=
  \idelim b = c \with x: _ => a = x \by { base: ab, equality: bc };

\definition local[x, y: A, xy: x = y]: y = x :=
  \idelim x = y \with z: _ => z = x \by { base: \refl(x), equality: xy };
```

## indexed match constraints

Holes can be inferred from branch constraints of indexed constructors.

```toml case
id = "accept-metavariables.indexed_match_constraints"
scope = "module"
expect = "accept"
name = "IndexedMatch"
parameters = '''A: \Set, x: A'''
```

```ref
\inductive Family: \forall (index: A) -> \Set :=
| member: \forall (y: A) -> Family y
;

\definition identity: Family x -> Family x :=
  \fun (h: _) =>
    \match h \in Family
      \return (\fun (y: A) => \fun (_: Family y) => Family y) \with {
    | member y : Family::member _
    };

\definition local [y: A]: Family y -> Family y :=
  \fun (h: _) =>
    \match h \in Family
      \return (\fun (z: A) => \fun (_: Family z) => Family z) \with {
    | member z : Family::member _
    };

\definition motiveHole: Family x -> Family x :=
  \fun (h: Family x) =>
    \match h \in Family
      \return (\fun (y: A) => \fun (_: _) => Family y) \with {
    | member y : Family::member _
    };
```

## inductive parameter inference

Inductive parameters can be inferred from constructor arguments.

```toml case
id = "accept-metavariables.inductive_parameter_inference"
scope = "module"
expect = "accept"
name = "MetaInductive"
parameters = '''A: \Set(0), a: A'''
```

```ref
\inductive Box[X: \Set(0)]: \Set(0) :=
  | box: X -> Box
;

\definition implicitBox: Box[A] := Box[_]::box a;
\definition namedImplicitBox: Box[A] := Box[_3]::box a;
```

## match constraints

Holes can be inferred from match scrutinee and branch constraints.

```toml case
id = "accept-metavariables.match_constraints"
scope = "module"
expect = "accept"
name = "MatchConstraints"
```

```ref
\inductive Or[P, Q: \Prop]: \Prop :=
| left: P -> Or
| right: Q -> Or
;

\structure PropEquiv[P, Q: \Prop]: \Prop := { lt: P -> Q, rt: Q -> P, };

\definition orAssoc [P, Q, R: \Prop]:
  PropEquiv[Or[Or[P, Q], R] \assign _1, Or[P, Or[Q, R]] \assign _2] :=
  PropEquiv[_1, _2] {
    lt := \fun (h: _) =>
      \match h \in Or \return (\fun (_: Or[Or[P, Q], R]) => Or[P, Or[Q, R]]) \with {
      | left inner :
          \match inner \in Or \return (\fun (_: Or[P, Q]) => Or[P, Or[Q, R]]) \with {
          | left p : Or[P, Or[Q, R]]::left p
          | right q : Or[P, Or[Q, R]]::right (Or[Q, R]::left q)
          }
      | right r : Or[P, Or[Q, R]]::right (Or[Q, R]::right r)
      },
    rt := \fun (h: _) =>
      \match h \in Or \return (\fun (_: Or[P, Or[Q, R]]) => Or[Or[P, Q], R]) \with {
      | left p : Or[_, _]::left (Or[_, _]::left p)
      | right inner :
          \match inner \in Or \return (\fun (_: Or[Q, R]) => Or[Or[P, Q], R]) \with {
          | left q : Or[_, _]::left (Or[_, _]::right q)
          | right r : Or[_, _]::right r
          }
      }
  };
```

## program annotations

Program annotations and expected types describe the same value and computation types.

```toml case
id = "accept-metavariables.program_annotations"
scope = "module"
expect = "accept"
name = "MetaProgram"
parameters = '''A: \VType, a: A'''
```

```ref
\definition finished: \RunStep[A, A] :=
  \finish[_, A](a);

\definition identity: (A ~> \F(A)) :=
  (\cfun (x: _) => \return(x));

\definition sequenced: \F(A) :=
  (\bind x: _ <- \return(a) \in \return(x));

\infer (\bind x: _ <- \return(a) \in \return(x));
\eval (\bind x: _ <- \return(a) \in \return(x));
\normalize (\bind x: _ <- \return(a) \in \return(x));
```

## program constructor inference

Program constructor parameters can be inferred from expected types.

```toml case
id = "accept-metavariables.program_constructor_inference"
scope = "module"
expect = "accept"
name = "MetaProgramConstructor"
parameters = '''A: \VType, a: A'''
```

```ref
\inductive Box[X: \VType]: \VType :=
  | box: X -> Box
;

\definition implicitBox: Box[A] := Box[_]::box a;
\definition namedImplicitBox: Box[A] := Box[_10]::box a;

\infer Box[_]::box a;
```

## program type inference

Program type arguments can be inferred from application constraints.

```toml case
id = "accept-metavariables.program_type_inference"
scope = "module"
expect = "accept"
name = "MetaProgramTypeInference"
parameters = '''A: \VType, a: A'''
```

```ref
/* Program terms determine a metavariable expected type in their category. */
\definition inferredValueType: _ := a;
\definition inferredComputationType: _ := \return(a);

\check a: _;
\check \return(a): _;
```


## Assigned record types and projections

A record type shared through assign can serve as the expected type for binders and projections.

```toml case
id = "explicit_meta_assignment_shares_record_types_before_projection"
scope = "module"
expect = "accept"
name = "Assignment"
```

```ref
\structure And[P, Q: \Prop]: \Prop := { left: P, right: Q, };
\structure PropEquiv[P, Q: \Prop]: \Prop := { lt: P -> Q, rt: Q -> P, };
\definition andAssoc [P, Q, R: \Prop]: PropEquiv[And[And[P, Q], R] \assign _1, And[P, And[Q, R]] \assign _2] := PropEquiv[_1, _2] {
  lt := \block {
    \fun (h: _1) \then
    \let p: P := h.left.left \then
    \let q: Q := h.left.right \then
    \let r: R := h.right \then
    \return And[_, _]::# p (And[_, _]::# q r)
  },
  rt := \block {
    \fun (h: _2) \then
    \let p: P := h.left \then
    \let q: Q := h.right.left \then
    \let r: R := h.right.right \then
    \return And[_, _]::# (And[_, _]::# p q) r
  },
};
```

## Program let annotations / 1

The let annotation differs from the value's type.

```toml case
id = "wrong-program-let-0"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition result: \F(A) := (\let x: B := a \in \return(a));
```

## Program let annotations / 2

A value is written in a let type annotation.

```toml case
id = "wrong-program-let-1"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition result: \F(A) := (\let x: a := a \in \return(a));
```

## Program let annotations / 3

No constraints determine the let value or its type.

```toml case
id = "wrong-program-let-2"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \VType, B: \VType, a: A'''
```

```ref
\definition result: \F(A) := (\let x: _ := ? \in \return(a));
```

## Reassigning inference variables / A

The same type is assigned again.

```toml case
id = "reassign-meta-A"
scope = "module"
expect = "accept"
name = "Assignment"
parameters = '''A: \Set, B: \Set, a: A'''
```

```ref
\definition value: A \assign _1 := a; \definition repeated: (A \assign _1) -> (A \assign _1) := \fun (x: A) => x;
```

## Reassigning inference variables / B

A different type B is assigned to an inference variable already determined to be A.

```toml case
id = "reassign-meta-B"
scope = "module"
expect = "reject"
name = "Assignment"
parameters = '''A: \Set, B: \Set, a: A'''
```

```ref
\definition value: A \assign _1 := a; \definition repeated: (A \assign _1) -> (B \assign _1) := \fun (x: A) => x;
```

## Match constraints / 1

The motive type differs from the scrutinee type.

```toml case
id = "match-constraint-mismatch-0"
scope = "module"
expect = "reject"
name = "MatchConstraints"
```

```ref
\inductive Or[P, Q: \Prop]: \Prop :=
  | left: P -> Or
| right: Q -> Or
;

\structure PropEquiv[P, Q: \Prop]: \Prop := { lt: P -> Q, rt: Q -> P, };

\definition orAssoc [P, Q, R: \Prop]:
  PropEquiv[Or[Or[P, Q], R] \assign _1, Or[P, Or[Q, R]] \assign _2] :=
  PropEquiv[_1, _2] {
  lt := \fun (h: _) =>
  \match h \in Or \return (\fun (_: Or[Or[P, Q], R]) => Or[P, Or[Q, R]]) \with {
    | left inner :
      \match inner \in Or \return (\fun (_: Or[P, Q]) => Or[P, Or[Q, R]]) \with {
      | left p : Or[P, Or[Q, R]]::left p
      | right q : Or[P, Or[Q, R]]::right (Or[Q, R]::left q)
    }
    | right r : Or[P, Or[Q, R]]::right (Or[Q, R]::right r)
  },
  rt := \fun (h: _) =>
  \match h \in Or \return (\fun (_: Or[P, Q]) => Or[Or[P, Q], R]) \with {
    | left p : Or[_, _]::left (Or[_, _]::left p)
    | right inner :
      \match inner \in Or \return (\fun (_: Or[Q, R]) => Or[Or[P, Q], R]) \with {
      | left q : Or[_, _]::left (Or[_, _]::right q)
      | right r : Or[_, _]::right r
    }
  }
};
```

## Match constraints / 2

A branch value differs from the corresponding constructor argument's type.

```toml case
id = "match-constraint-mismatch-1"
scope = "module"
expect = "reject"
name = "MatchConstraints"
```

```ref
\inductive Or[P, Q: \Prop]: \Prop :=
  | left: P -> Or
| right: Q -> Or
;

\structure PropEquiv[P, Q: \Prop]: \Prop := { lt: P -> Q, rt: Q -> P, };

\definition orAssoc [P, Q, R: \Prop]:
  PropEquiv[Or[Or[P, Q], R] \assign _1, Or[P, Or[Q, R]] \assign _2] :=
  PropEquiv[_1, _2] {
  lt := \fun (h: _) =>
  \match h \in Or \return (\fun (_: Or[Or[P, Q], R]) => Or[P, Or[Q, R]]) \with {
    | left inner :
      \match inner \in Or \return (\fun (_: Or[P, Q]) => Or[P, Or[Q, R]]) \with {
      | left p : Or[P, Or[Q, R]]::left p
      | right q : Or[P, Or[Q, R]]::right (Or[Q, R]::left q)
    }
    | right r : Or[P, Or[Q, R]]::right (Or[Q, R]::right r)
  },
  rt := \fun (h: _) =>
  \match h \in Or \return (\fun (_: Or[P, Or[Q, R]]) => Or[Or[P, Q], R]) \with {
    | left p : Or[_, _]::left (Or[_, _]::left p)
    | right inner :
      \match inner \in Or \return (\fun (_: Or[Q, R]) => Or[Or[P, Q], R]) \with {
      | left q : Or[_, _]::left (Or[_, _]::right q)
      | right r : Or[_, _]::left r
    }
  }
};
```
