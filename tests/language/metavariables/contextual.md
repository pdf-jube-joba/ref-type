# Inferring functions with local contexts

## Contextual argument

A function can be passed as a module argument after inferring a lambda annotation inside a definition.

```toml case
id = "contextual-argument"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module ContextualArgument {
  \structure Carrier := { A: \Set, };
  \definition identity[C: Carrier]: C.A -> C.A := \fun (x: _) => x;
  \module Pass(A: \Set, f: A -> A) {
    \definition value: A -> A := f;
  }
  \inductive Unit: \Set := | unit: Unit;
  \definition C: Carrier := Carrier { A := Unit };
  \import \root.ContextualArgument[].Pass[A := C.A, f := identity C] \as P;
  \definition value: Unit -> Unit := P.value;
}
```

## Bound argument

A function value bound with a type can also be passed as a module argument.

```toml case
id = "bound-argument"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module BoundArgument {
  \structure Carrier := { A: \Set, };
  \definition identity[C: Carrier]: C.A -> C.A := \fun (x: _) => x;
  \module Pass(A: \Set, f: A -> A) {
    \definition value: A -> A := f;
  }
  \inductive Unit: \Set := | unit: Unit;
  \definition C: Carrier := Carrier { A := Unit };
  \definition bound: C.A -> C.A := identity C;
  \import \root.BoundArgument[].Pass[A := C.A, f := bound] \as P;
  \definition value: Unit -> Unit := P.value;
}
```

## Contextual inference

The type of an inner lambda can be inferred from the expected type of an application taking a function argument.

```toml case
id = "contextual-inference"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\macro congr($A, $B) :=
  (\fun (law: \forall (f: $A -> $B) -> \forall (a, b: $A) -> a = b -> f a = f b) => law)
(\fun (f: $A -> $B) => \fun (a, b: $A) => \fun (e: a = b) =>
\idelim a = b \with x: $A => f a = f x \by { base: \refl(f a), equality: e });

\definition identity[n: A]: A := n;
\definition mapping: A -> A := \fun (n: A) => n;
\definition End: \Set := A -> A;
\definition matches[n: A]: identity (mapping n) = identity (mapping n) :=
  congr!{End A} (\fun (f: _) => identity (f n)) _ _ (\refl(mapping));
```

## Infer projection

An expected record type can fill a binder hole and allow field projection.

```toml case
id = "infer-projection"
scope = "module"
expect = "accept"
```

```ref
\structure And[P, Q: \Prop]: \Prop := { left: P, right: Q, };
\definition andElim[P, Q, R: \Prop]: (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value.left) (value.right);
```

## Infer take continuation

Expected types can also infer the types of later functions using an existentially eliminated witness.

```toml case
id = "infer-take-continuation"
scope = "module"
expect = "accept"
name = "InferTake"
parameters = '''A: \Set, P: \Prop'''
```

```ref
\definition elim: (\exists A) -> (A -> P) -> P :=
  \fun (e: _) (step: _) => \block {
  \takefrom x: A \by e \then
  \return step x
};
```

## Infer subset

A binder can be inferred from an expected subset type and used with a function over the base type and a membership proof.

```toml case
id = "infer-subset"
scope = "module"
expect = "accept"
name = "InferSubset"
parameters = '''A: \Set, P: A -> \Prop, f: A -> A'''
```

```ref
\definition Parameter: \Set := \Cast[A] ({ x: A \where P x });
\definition apply: Parameter -> A := \fun (t: _) => f t;
\definition property: \forall (t: Parameter) -> P t :=
  \fun (t: _) => (\fun (unused: A) => \bysub(A, Parameter, t)) (f t);
```

## Contextual inference with repeated arguments

Even in an application with repeated arguments, the function argument's type can be inferred from the expected type.

```toml case
id = "contextual-function-inference-with-repeated-arguments"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\macro congr($A, $B) :=
  (\fun (law: \forall (f: $A -> $B) -> \forall (a, b: $A) -> a = b -> f a = f b) => law)
(\fun (f: $A -> $B) => \fun (a, b: $A) => \fun (e: a = b) =>
\idelim a = b \with x: $A => f a = f x \by { base: \refl(f a), equality: e });
\definition identity[n: A]: A := n;
\definition mapping: A -> A -> A := \fun (n, m: A) => n;
\definition Binary: \Set := A -> A -> A;
\definition matches[n: A]: identity (mapping n n) = identity (mapping n n) :=
  congr!{Binary A} (\fun (f: _) => identity (f n n)) _ _ (\refl(mapping));
```

## Imported front definitions still check argument types

The inferred function is passed as a function over a different inductive type.

```toml case
id = "imported-front-definitions-still-check-argument-types"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module ImportedFrontDefinitionsStillCheck {
  \structure Carrier := { A: \Set, };
  \definition identity[C: Carrier]: C.A -> C.A := \fun (x: _) => x;
  \inductive Unit: \Set := | unit: Unit;
  \inductive Other: \Set := | other: Other;
  \definition C: Carrier := Carrier { A := Unit };
  \module Pass(f: Other -> Other) {}
  \import \root.ImportedFrontDefinitionsStillCheck[].Pass[f := identity C] \as P;
}
```

## Wrong inferred proof

A proof of P is returned as a proof of Q.

```toml case
id = "wrong-inferred-proof"
scope = "module"
expect = "reject"
parameters = '''P, Q: \Prop'''
```

```ref
\definition bad: P -> Q := \fun (p: _) => p;
```

## Escaping inferred witness

A witness extracted from an existential escapes into the result.

```toml case
id = "escaping-inferred-witness"
scope = "module"
expect = "reject"
parameters = '''A: \Set'''
```

```ref
\definition bad: (\exists A) -> A := \fun (e: _) => \block { \takefrom x: A \by e \then \return x };
```

## Unproved inferred subset

A base-type value is returned as a subset value without a membership proof.

```toml case
id = "unproved-inferred-subset"
scope = "module"
expect = "reject"
parameters = '''A: \Set, P: A -> \Prop'''
```

```ref
\definition Sub: \Set := \Cast[A] ({ x: A \where P x });
\definition bad: A -> Sub := \fun (x: _) => x;
```

## Module arguments / hole

An inference hole appears directly in a module argument.

```toml case
id = "module-argument-hole"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module ModuleArgumentHole {
  \inductive Unit: \Set := | unit: Unit;
  \module Pass(f: Unit -> Unit) {}
  \import \root.ModuleArgumentHole[].Pass[f := _] \as P;
}
```

## Module arguments / lambda-hole

An inference hole appears directly in a module argument.

```toml case
id = "module-argument-lambda-hole"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module ModuleArgumentLambdaHole {
  \inductive Unit: \Set := | unit: Unit;
  \module Pass(f: Unit -> Unit) {}
  \import \root.ModuleArgumentLambdaHole[].Pass[f := \fun (x: _) => x] \as P;
}
```

## Equalities whose application spines change under beta reduction

Outer application arguments must not be equated before the function heads match.
Both holes can be inferred from the equality after reduction.

```toml case
id = "beta-spine-inference"
scope = "module"
expect = "accept"
parameters = '''V: \Set, op: V -> V -> V, a, b: V'''
```

```ref
\definition law: ((\fun (w: V) => op w b) a) = op a b := \refl(op _ _);
```
