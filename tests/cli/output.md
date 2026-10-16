# cli / output

## 大きな出力

多数の query を含む入力の検査が完了する。

```toml case
id = "large-output"
scope = "module"
expect = "accept"
```

```ref repeat=10000
\infer \Set;
```

## trace を有効にした検査

trace の有無によらず、同じ入力を受理する。

```toml scenario
id = "trace-output"
scope = "module"
```

### 通常

命題の定義と query を受理する。

```toml step
id = "normal"
expect = "accept"
```

```ref file=Test.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P;
```

### trace

trace を有効にしても受理する。

```toml step
id = "trace"
expect = "accept"
args = ["--trace"]
```

