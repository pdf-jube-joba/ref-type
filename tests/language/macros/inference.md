# Inference through macro expansion

## Holes passed to equality-elimination captures

Holes in the same capture at equality endpoints, in a motive under binders, and in the base case are inferred from the equality proof.

```toml case
id = "captured-hole-equality-elimination"
scope = "module"
expect = "accept"
parameters = '''A, B: \Set'''
```

```ref
\macro map_eq($f, $a, $b, $same) :=
  \idelim $a = $b \with x: A => $f $a = $f x
    \by { base: \refl($f $a), equality: $same };
\definition law[f: A -> B][a, b: A][same: a = b]: f a = f b :=
  map_eq!{f _ _ same};
```

## Equality elimination through recursive macro expansion

Holes passed through sequence captures and token matches are also shared between the motive and base case.

```toml case
id = "forwarded-captured-hole"
scope = "module"
expect = "accept"
parameters = '''A, B: \Set'''
```

```ref
\macro map_eq($f, $a, $b, $same) :=
  \idelim $a = $b \with x: A => $f $a = $f x
    \by { base: \refl($f $a), equality: $same };
\macro forward(..args) := \tmatch args {
  | ($f, $a, $b, $same) => map_eq!{$f $a $b $same}
};
\definition law[f: A -> B][a, b: A][same: a = b]: f a = f b :=
  forward!{f _ _ same};
```

## Conflicting constraints on one hole

A hole in the same capture cannot be solved as two different local variables.

```toml case
id = "captured-hole-inconsistent-constraints"
scope = "module"
expect = "reject"
parameters = '''A: \Set, a, b: A'''
```

```ref
\macro duplicate($x) := \fun (h: $x = a) => \refl($x);
\definition impossible: (a = a) -> b = b := duplicate!{_};
```

## Separate calls and named holes

Holes from separate macro calls within a declaration and explicit named holes are each solved from their expected types.

```toml case
id = "captured-hole-independent-calls"
scope = "module"
expect = "accept"
parameters = '''A: \Set, a, b: A'''
```

```ref
\structure Both: \Prop := {
  left: a = a,
  right: b = b,
  named: b = b,
};
\macro infer($x) := \refl($x);
\definition independent: Both := Both {
  left := infer!{_},
  right := infer!{_},
  named := \refl(_0),
};
```

## Bound variables inside captures

Duplicated lambdas compare their entire expressions under binders rather than requiring identical internal variable names.

```toml case
id = "captured-lambda-body-hole"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\definition identity: A -> A := \fun (x: A) => x;
\macro copy($f) := \fun (h: $f = identity) => \refl($f);
\definition law: (identity = identity) -> identity = identity :=
  copy!{{\fun (x: A) => _}};
```

## Multiple internal binders and forwarding

Forwarding a lambda with holes in its annotation and body still gives matching duplicated function values.

```toml case
id = "forwarded-captured-nested-lambda"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\definition first: A -> A -> A := \fun (x, y: A) => x;
\macro copy($f) := \fun (h: $f = first) => \refl($f);
\macro forward(..args) := \tmatch args { | ($f) => copy!{$f} };
\definition law: (first = first) -> first = first :=
  forward!{{\fun (x: _) => \fun (y: _) => _}};
```

## Program captures and expected types

Capture sharing does not prevent inference from propagating expected types into Program function annotations.

```toml case
id = "program-capture-expected-function"
scope = "module"
expect = "accept"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\macro keep($x) := $x;
\definition identity: Bool -> Bool := keep!{{\fun (x: _) => \return(x)}};
\definition value: Bool := keep!{{Bool::true \of _}};
```

## Program application heads

Capture sharing does not turn lambdas or ascribed computations into values requiring an explicit force.

```toml case
id = "program-capture-application-head"
scope = "module"
expect = "accept"
parameters = '''A: \VType, a: A'''
```

```ref
\definition identity: A -> A := \fun (x: A) => \return(x);
\macro call($f) := $f a;
\definition lambda: \F(A) := call!{{\fun (x: _) => \return(x)}};
\definition ascribed: \F(A) := call!{{identity \of _}};
\definition computationLambda: \F(A) := call!{{\cfun (x: _) => \return(x)}};
\definition forced: \F(A) := call!{{\force(\thunk(\fun (x: _) => \return(x)))}};
```

## Program type and value captures

Expected types and shared values are matched in type, computation-type, value, and computation positions.

```toml case
id = "program-capture-categories"
scope = "module"
expect = "accept"
parameters = '''A: \VType, a: A'''
```

```ref
\macro keep($x) := $x;
\check a: keep!{_};
\check \return(a): keep!{{\F(_)}};
\definition value: A := keep!{{a \of _}};
\definition computation: \F(A) := keep!{{\return(a \of _)}};
```

## Nested equational reasoning and proof types

Intermediate expressions through nested congruence and commutativity arguments are inferred from the surrounding equational reasoning.

```toml case
id = "captured-proof-type-constraints"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module NestedEquality(A, Index: \Set, combine: A -> A -> A, select: Index -> A -> A, transform: A -> A,
  seed, other, source, result: A, a, b: Index,
  commutes: \forall (x, y: A) -> combine x y = combine y x,
  join: source = combine (select a seed) other,
  same: select a seed = select b seed,
  transformed: select b seed = transform seed,
  final: result = combine other (transform seed)) {
  \macro sym($A) :=
    (\fun (law: \forall (a, b: $A) -> a = b -> b = a) => law)
    (\fun (a, b: $A)(e: a = b) =>
      \idelim a = b \with x: $A => x = a \by { base: \refl(a), equality: e });
  \macro trans($A) :=
    (\fun (law: \forall (a, b, c: $A) -> a = b -> b = c -> a = c) => law)
    (\fun (a, b, c: $A)(ab: a = b)(bc: b = c) =>
      \idelim b = c \with x: $A => a = x \by { base: ab, equality: bc });
  \macro eq_reason_in($A, $a, ..steps) := \tmatch steps {
    | () => \refl($a)
    | ("=", $b, "by", $h, ..rest) =>
        trans!{$A} $a $b _ $h (eq_reason_in!{$A $b ..rest})
  };
  \macro congr($A, $B) := \fun (f: $A -> $B)(a, b: $A)(same: a = b) =>
    \idelim a = b \with x: $A => f a = f x \by { base: \refl(f a), equality: same };
  \definition law: source = result := eq_reason_in!{A _
    "=" _ "by" { join }
    "=" _ "by" { congr!{A A} (\fun (w: A) => combine w other) _ _ (eq_reason_in!{A _
      "=" _ "by" { same }
      "=" _ "by" { transformed }
    }) }
    "=" _ "by" { commutes _ _ }
    "=" _ "by" { sym!{A} _ _ final }
  };
}
```
