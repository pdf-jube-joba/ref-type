# basics / cases

## ambiguity

Declarations of same-named modules with different telescopes can each be parsed.

```toml case
id = "accept-ambiguity"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module A {}

\module A () {}

\module A (
    X: \Set(0)
) {}

\module A (
    X: \Set(0),
) {}
```

## definition

A definition can reference module parameters and preceding definitions.

```toml case
id = "accept-definition"
scope = "module"
expect = "accept"
name = "Hello"
parameters = '''A: \Set(0),'''
```

```ref
\definition B: \Set(0) := A;
\definition C: \Set(0) := A;
\definition D: \Set(0) := B;
```

## eval id

Application of the identity function can be evaluated.

```toml case
id = "accept-eval_id"
scope = "module"
expect = "accept"
name = "Example"
```

```ref
\eval (\fun (x: \SetKind) => x) \Set;
```

## hello world

An empty module without declarations is also valid.

```toml case
id = "accept-hello_world"
scope = "module"
expect = "accept"
name = "HelloWorld"
```

```ref

```

