# cache / workspace

## workspace の共有キャッシュ

一つの member を検査した結果は、別の member と workspace 全体の検査でも共有依存の検証結果として再利用される。

```toml scenario
id = "shared-workspace"
scope = "workspace"
cache_dir = "default"
```

```toml file=ref.toml
[workspace]
packages = ['base', 'left', 'right']
```

```toml file=base/ref.toml
[package]
name = 'base'
```

```ref file=base/src/root.ref
\module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
```

```toml file=left/ref.toml
[package]
name = 'left'
[dependencies]
base = {path = '../base'}
```

```ref file=left/src/root.ref
\module Main { \import base.Core[] \as B; \definition p: \Prop := B.P; \infer p; }
```

```toml file=right/ref.toml
[package]
name = 'right'
[dependencies]
base = {path = '../base'}
```

```ref file=right/src/root.ref
\module Main { \import base.Core[] \as B; \definition p: \Prop := B.P; \infer p; }
```

### left

最初の member を検査する。

```toml step
id = "left"
expect = "accept"
cache = "unused"
entry = "left"
```

### right

別の member で共有する依存を再利用する。

```toml step
id = "right"
expect = "accept"
cache = "reused"
entry = "right"
cwd = "right"
```

### workspace

両方の member が持つ検証結果を再利用する。

```toml step
id = "workspace"
expect = "accept"
cache = "reused"
```

### 再検査

workspace 全体の再検査でも再利用する。

```toml step
id = "warm"
expect = "accept"
cache = "reused"
```

### 一覧

workspace の module 一覧の取得は成功する。

```toml step
id = "listing"
expect = "accept"
args = ["--list-modules"]
```

### member を選択

workspace から一つの member を選んでも再利用する。

```toml step
id = "selected"
expect = "accept"
cache = "reused"
args = ["--module", "right"]
```

### 保存先の指定

明示した別の保存先には検証結果がない。

```toml step
id = "custom"
expect = "accept"
cache = "unused"
entry = "left"
cache_dir = "custom-cache"
```

### 保存先の再利用

指定した保存先でも別の member に共有できる。

```toml step
id = "custom-right"
expect = "accept"
cache = "reused"
entry = "right"
cache_dir = "custom-cache"
```

## 個別の検査と選択範囲の変更

依存先を個別に検査してから、その依存を持つ別の package の module を選択しても型の同一性と検証結果を保つ。

```toml scenario
id = "dependency-selection"
scope = "workspace"
```

```toml file=ref.toml
[workspace]
packages = ['base', 'aaa', 'app']
```

```toml file=base/ref.toml
[package]
name = 'base'
```

```ref file=base/src/root.ref
\module Core {
            \inductive Unit: \Set := | unit: Unit;
            \definition id[x: Unit]: Unit := x;
        }
        \module Unused { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
```

```toml file=aaa/ref.toml
[package]
name = 'aaa'
```

```ref file=aaa/src/root.ref
\module Core { \inductive Unit: \Set := | unit: Unit; }
```

```toml file=app/ref.toml
[package]
name = 'app'
[dependencies]
aaa = {path = '../aaa'}
base = {path = '../base'}
```

```ref file=app/src/root.ref
\module Main {
        \import base.Core[] \as B;
        \import aaa.Core[] \as N;
        \definition value: B.Unit := B.id B.Unit::unit;
        \definition other: N.Unit := N.Unit::unit;
        \definition law: value = B.Unit::unit := \refl(B.Unit::unit);
        \infer value;
    }
```

### base

base を個別に検査する。

```toml step
id = "base"
expect = "accept"
cache = "unused"
entry = "base"
```

### aaa

独立した aaa を個別に検査する。

```toml step
id = "aaa"
expect = "accept"
cache = "unused"
entry = "aaa"
```

### app の選択

先に検査した依存先を再利用する。

```toml step
id = "app"
expect = "accept"
cache = "reused"
entry = "app"
args = ["--module", "app.Main"]
```

### app の再検査

選択範囲の検証結果を再利用する。

```toml step
id = "warm"
expect = "accept"
cache = "reused"
entry = "app"
args = ["--module", "app.Main"]
```

### 順序の変更

workspace の列挙順を変えても同じ型と検証結果を利用できる。

```toml step
id = "order"
expect = "accept"
cache = "reused"
```

```toml file=ref.toml
[workspace]
packages = ['app', 'base', 'aaa']
```

