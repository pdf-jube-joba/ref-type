# cache / module

## 別プロセスでの再利用と編集

同じ module を再検査すると保存された検証結果を再利用する。変更した内容は現在のソースとして検査する。

```toml scenario
id = "module-cache"
scope = "module"
```

```ref file=Test.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P;
```

### 初回

空のキャッシュなので検証結果の再利用はない。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

### 再検査

同じ検証結果を再利用し、query の結果も保つ。

```toml step
id = "warm"
expect = "accept"
cache = "reused"
stdout_same_as = "cold"
```

### 強制検査

以前の検証結果を再利用せずに検査する。

```toml step
id = "full"
expect = "accept"
cache = "unused"
args = ["--full-check"]
stdout_same_as = "cold"
```

### 変更

集合を命題として定義しているため拒否される。

```toml step
id = "changed"
expect = "reject"
```

```ref file=Test.ref
\definition P: \Prop := \Set;
```

### キャッシュ無効

同じ不正な内容はキャッシュを無効にしても拒否される。

```toml step
id = "uncached"
expect = "reject"
cache = "unused"
args = ["--no-cache"]
stdout_same_as = "changed"
```

### 修正

型が合う内容に修正すると受理される。

```toml step
id = "fixed"
expect = "accept"
```

```ref file=Test.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P;
```

### 修正後の再検査

修正後の検証結果を再利用する。

```toml step
id = "fixed-warm"
expect = "accept"
cache = "reused"
stdout_same_as = "fixed"
```

### 保存先の変更

異なる空のキャッシュでは再利用しない。

```toml step
id = "other-cache"
expect = "accept"
cache = "unused"
cache_dir = "other-cache"
```

### 元の保存先

元の保存先には検証結果が残っている。

```toml step
id = "original-cache"
expect = "accept"
cache = "reused"
```

### 消去

キャッシュを消去すると再利用せずに検査する。

```toml step
id = "clear"
expect = "accept"
cache = "unused"
args = ["--clear-cache"]
```

### 消去後

消去後に保存した検証結果を再利用する。

```toml step
id = "after-clear"
expect = "accept"
cache = "reused"
```

## 入力に対応する既定のキャッシュ

単独ファイルの既定のキャッシュは、起動する作業ディレクトリを変更しても再利用される。

```toml scenario
id = "default-file-cache"
scope = "module"
cache_dir = "default"
```

```ref file=Test.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P;
```

```text file=elsewhere/placeholder.txt
working directory
```

### 初回

初回は検証結果を保存する。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

### 別の作業ディレクトリ

入力ファイルのキャッシュを再利用する。

```toml step
id = "other-cwd"
expect = "accept"
cache = "reused"
cwd = "elsewhere"
stdout_same_as = "cold"
```

