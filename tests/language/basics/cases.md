# basics / cases

## ambiguity

異なる telescope を持つ同名 module の宣言がそれぞれ解析できるため、受理される。

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

definition は module parameter と先行する definition を参照できるため、受理される。

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

恒等関数の application が元の引数に簡約されるため、受理される。

```toml case
id = "accept-eval_id"
scope = "module"
expect = "accept"
stdout = "\\Set(0)\n"
name = "Example"
```

```ref
\eval (\fun (x: \SetKind) => x) \Set;
```

## hello world

宣言のない空の module も成立するため、受理される。

```toml case
id = "accept-hello_world"
scope = "module"
expect = "accept"
name = "HelloWorld"
```

```ref

```

