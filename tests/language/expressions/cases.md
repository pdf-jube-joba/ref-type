# Polymorphic expressions

## Polymorphic functions at different universes

An identity at a higher universe can be instantiated with the type of lower-universe identity functions. A separate query infers the type of a function that takes an endomorphism and returns a type.

```toml case
id = "polymorphic-functions-at-different-universes"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module PolymorphicIdentity {
    \definition Identity: \Set(1) := \forall (X: \Set(0)) -> \forall (x: X) -> X;
    \definition identity: Identity := \fun (X: \Set(0)) => \fun (x: X) => x;
    \definition identityHigher: \forall (X: \Set(1)) -> \forall (x: X) -> X := \fun (X: \Set(1)) => \fun (x: X) => x;
    \definition identityOnFunctions: Identity -> Identity := identityHigher Identity;
}

\module HigherOrderType (
    A: \Set(0),
) {
    \infer \fun (_: A -> A) => A;
}
```

