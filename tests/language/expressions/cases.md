# expressions / cases

## expressions

項と binder と application の各構文を対応する型で使えるため、受理される。

```toml case
id = "accept-expressions.expressions"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Test1 {
    \definition Idtype: \Set(1) := \forall (X: \Set(0)) -> \forall (x: X) -> X;
    \definition id: Idtype := \fun (X: \Set(0)) => \fun (x: X) => x;
    \definition id2: \forall (X: \Set(1)) -> \forall (x: X) -> X := \fun (X: \Set(1)) => \fun (x: X) => x;
    \definition a: Idtype -> Idtype := id2 Idtype;
}

\module Test2 (
    A: \Set(0),
    P: A -> \Prop,
    x: A,
    l: P x,
) {
    \infer \fun (_: A -> A) => A;
}
```

