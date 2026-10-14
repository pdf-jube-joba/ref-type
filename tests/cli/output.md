# cli / output

## 大きな出力

多数の query の結果を欠落や停止なく受け取れる。

```toml case
id = "large-output"
scope = "module"
expect = "accept"
stdout_lines = 10000
stdout_bytes_min = 65537
```

```ref repeat=10000
\infer \Set;
```

## trace と標準出力

trace は標準エラーに出力され、query の標準出力は通常の実行と同じになる。

```toml scenario
id = "trace-output"
scope = "module"
```

### 通常

恒等関数の値を表示できる。

```toml step
id = "normal"
expect = "accept"
```

```ref file=Test.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P;
```

### trace

同じ query の結果を返す。

```toml step
id = "trace"
expect = "accept"
args = ["--trace"]
stdout_same_as = "normal"
stderr_empty = false
```

