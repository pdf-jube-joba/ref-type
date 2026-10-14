# cache / dependencies

## 推移的な依存と再検査

C が B に、B が A に依存する場合、依存先の検証結果を再利用しつつ現在のソースの変更を検出する。

```toml scenario
id = "transitive"
scope = "package"
entry = "c"
```

```toml file=a/ref.toml
[package]
name = "a"
```

```ref file=a/src/root.ref
\module Base;
```

```ref file=a/src/Base.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

```toml file=b/ref.toml
[package]
name = "b"
[dependencies]
a = { path = "../a" }
```

```ref file=b/src/root.ref
\module Bridge { \import a.Base[] \as A; \definition P: \Prop := A.P; }
```

```toml file=c/ref.toml
[package]
name = "c"
[dependencies]
b = { path = "../b" }
```

```ref file=c/src/root.ref
\module Client { \import b.Bridge[] \as B; \infer B.P; } \module Independent { \module Child { \infer \Set; } }
```

### 初回

依存する宣言の型が合うため受理される。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
args = ["--full-check-local"]
```

### 入口の再検査

入口を再検査し、依存先の検証結果を再利用する。

```toml step
id = "local"
expect = "accept"
cache = "reused"
args = ["--full-check-local"]
stdout_same_as = "cold"
```

### 通常の再検査

通常の検査でも再利用できる。

```toml step
id = "warm"
expect = "accept"
cache = "reused"
```

### 推移的な依存の変更

A の不正な宣言を検出して拒否する。

```toml step
id = "edit"
expect = "reject"
```

```ref file=a/src/Base.ref
\definition P: \Prop := \Set;
```

### 入口を再検査

依存先も変更されているため拒否する。

```toml step
id = "local-error"
expect = "reject"
args = ["--full-check-local"]
```

### 全体を再検査

キャッシュによる省略をしなくても拒否する。

```toml step
id = "full-error"
expect = "reject"
cache = "unused"
args = ["--full-check"]
```

### キャッシュ無効

キャッシュを無効にしても拒否する。

```toml step
id = "no-cache-error"
expect = "reject"
cache = "unused"
args = ["--no-cache"]
```

### 依存先を修正

A を修正すると再び受理される。

```toml step
id = "repair"
expect = "accept"
args = ["--full-check-local"]
```

```ref file=a/src/Base.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

### 入口の変更

入口自身の不正な宣言も拒否する。

```toml step
id = "entry-error"
expect = "reject"
args = ["--full-check-local"]
```

```ref file=c/src/root.ref
\module Client { \definition bad: \Prop := \Set; }
```

