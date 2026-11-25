# Box parameters and residual terms

## Type and value module parameters

Terms blocked on input during Program reduction are reflected, and Logic beta reduction eliminates unnecessary inputs.
Parameters remaining in thunks inside return are reflected as well.

```toml case
id = "box-parameters.module"
scope = "module"
parameters = 'A: \VType, a: A, x: \U(\F(A))'
expect = "accept"
```

```ref
\definition boxed: \Box[\F(A)] := \box[_](
  \bind y: A <- \force x \in \return a);
\definition result: \squash[_](boxed) = a^ := \refl(a^);
\definition delayed: \Box[\F(\U(\F(A)))] :=
  \box[_](\return (\thunk (\force x)));
\definition delayedResult: \squash[_](delayed) = x^ := \refl(x^);
\definition identity: \Box[A ~> \F(A)] :=
  \box[_](\cfun (v: A) => \return v);
\definition application:
  \squash[_](\boxapp(identity, \box[_](\return a))) = a^ := \refl(a^);
```

## Definition arguments and instantiation

An ordinary definition takes a type and value to construct a Box.
Reflection and substitution agree before and after instantiation.

```toml case
id = "box-parameters.definition"
scope = "module"
expect = "accept"
```

```ref
\inductive Bit: \VType := | zero: Bit | one: Bit;
\definition package[A: \VType][a: A][x: \U(\F(A))]: \Box[\F(A)] :=
  \box[_](\bind y: A <- \force x \in \return a);
\definition residual[A: \VType][a: A][x: \U(\F(A))]:
  \squash[_](package A a x) = a^ := \refl(a^);
\definition concrete:
  \squash[_](package Bit Bit::one (\thunk (\return Bit::zero))) = Bit^::one :=
  residual Bit Bit::one (\thunk (\return Bit::zero));
\definition reflected[A: \VType][a: A]: A^ :=
  \squash[_](\box[_](\return a));
\definition substituted: reflected Bit Bit::one = Bit^::one := \refl(Bit^::one);
```

## Namespace instantiation

A module exposing a Box is instantiated with two values.

```toml case
id = "box-parameters.namespace"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Holder(A: \VType, boxed: \Box[\F(A)]) {
  \definition result: A^ := \squash[_](boxed);
}
\module Source(A: \VType, a: A, x: \U(\F(A))) {
  \definition boxed: \Box[\F(A)] :=
    \box[_](\bind y: A <- \force x \in \return a);
  \definition result: \squash[_](boxed) = a^ := \refl(a^);
  \import \root.Holder[A := A, boxed := boxed] \as Forward;
  \definition forwarded: Forward.result = a^ := \refl(a^);
}
\module Consumer {
  \inductive Bit: \VType := | zero: Bit | one: Bit;
  \import \root.Source[A := Bit, a := Bit::zero, x := \thunk (\return Bit::one)] \as Zero;
  \import \root.Source[A := Bit, a := Bit::one, x := \thunk (\return Bit::zero)] \as One;
  \definition zero: \squash[_](Zero.boxed) = Bit^::zero := Zero.result;
  \definition one: \squash[_](One.boxed) = Bit^::one := One.result;
  \definition forwarded: Bit^::one = Bit^::one := One.forwarded;
}
```

## Boxes in termination proofs

When reflecting Program definitions, parameters and Boxes referenced by termination proofs also move into the Logic context.

```toml case
id = "box-parameters.termination-proof"
scope = "module"
parameters = 'A: \VType, a: A'
expect = "accept"
```

```ref
\definition step: \U(A ~> \F(\RunStep[A, A])) :=
  \thunk (\cfun (s: A) => \return (\finish[A, A](a)));
\definition Terminates[s: A^]: \Prop :=
  \forall (P: A^ -> \Prop) ->
    (\forall (x: A^) ->
      (\step-match t: \RunStep[A^, A^] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step^ x) -> P x) -> P s;
\definition terminates: Terminates a^ :=
  \fun (P: _) (h: _) =>
    h (\squash[_](\box[_](\return a))) (\fun (Q: \Prop) (q: Q) => q);
\definition result: \F(A) := \run[A, A](step, a) \by { terminates };
\definition reflectedResult: result^ = a^ := \refl(a^);
```
