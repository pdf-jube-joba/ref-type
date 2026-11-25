# Basic declarations and queries

## Module headers with empty and nonempty parameter lists

Declarations of same-named modules with different telescopes can each be parsed.

```toml case
id = "module-header-variants"
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

## Definitions reference parameters and preceding declarations

A definition can reference module parameters and preceding definitions.

```toml case
id = "definitions-reference-earlier-declarations"
scope = "module"
expect = "accept"
parameters = '''A: \Set(0),'''
```

```ref
\definition B: \Set(0) := A;
\definition C: \Set(0) := A;
\definition D: \Set(0) := B;
```

## Evaluating an identity application

Application of the identity function can be evaluated.

```toml case
id = "evaluate-identity-application"
scope = "module"
expect = "accept"
parameters = '''A: \Set, a: A'''
```

```ref
\eval (\fun (x: A) => x) a;
```

## Empty modules

An empty module without declarations is also valid.

```toml case
id = "empty-module"
scope = "module"
expect = "accept"
```

```ref

```

