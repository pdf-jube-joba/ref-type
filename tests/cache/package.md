# cache / package

## 利用側の編集と module の再利用

利用側の module を変更しても、変更していない依存 module の検証結果は再利用できる。

```toml scenario
id = "module-dependency"
scope = "package"
```

```ref file=src/root.ref
\module Base; \module Use;
```

```ref file=src/Base.ref
\inductive Unit: \Set := | unit: Unit; \definition value: Unit := Unit::unit;
```

```ref file=src/Use.ref
\import \root.Base[] \as B; \infer B.value;
```

### 初回

正しい constructor と import な。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

### 利用側の変更

依存 module の検証結果を再利用して新しい定義を検査できる。

```toml step
id = "edit"
expect = "accept"
cache = "reused"
```

```ref file=src/Use.ref
\import \root.Base[] \as B; \definition copy: B.Unit := B.value; \normalize copy;
```

### キャッシュ無効

再利用せず検査しても同じ簡約結果になる。

```toml step
id = "clean"
expect = "accept"
cache = "unused"
args = ["--no-cache"]
stdout_same_as = "edit"
```

### 依存先の変更

依存先の値が不正になると利用側も受理できない。

```toml step
id = "dependency-error"
expect = "reject"
```

```ref file=src/Base.ref
\inductive Unit: \Set := | unit: Unit; \definition value: Unit := \Set;
```

### 依存先の修正

依存先を修正すれば再び受理される。

```toml step
id = "repair"
expect = "accept"
```

```ref file=src/Base.ref
\inductive Unit: \Set := | unit: Unit; \definition value: Unit := Unit::unit;
```

### 外部ファイルの削除

必要な外部 module のファイルがない。

```toml step
id = "missing-source"
expect = "reject"
remove = ["src/Base.ref"]
```

## 別の利用側と独立した依存

共通の依存先を持つ二つの package を経由した型は、別の利用側で成果物を復元しても同じ型として扱える。
利用側に独立した依存を追加しても、既存の依存先の検証結果を再利用する。

```toml scenario
id = "different-consumers"
scope = "package"
entry = "app"
```

```toml file=base/ref.toml
[package]
name = "base"
```

```ref file=base/src/root.ref
\module Core { \inductive Unit: \Set := | unit: Unit; }
```

```toml file=left/ref.toml
[package]
name = "left"
[dependencies]
base = { path = "../base" }
```

```ref file=left/src/root.ref
\module Core { \import base.Core[] \as B; \definition value: B.Unit := B.Unit::unit; }
```

```toml file=right/ref.toml
[package]
name = "right"
[dependencies]
base = { path = "../base" }
```

```ref file=right/src/root.ref
\module Core { \import base.Core[] \as B; \definition id(x: B.Unit): B.Unit := x; }
```

```toml file=app/ref.toml
[package]
name = "app"
[dependencies]
left = { path = "../left" }
right = { path = "../right" }
```

```ref file=app/src/root.ref
\module Main { \import left.Core[] \as L; \import right.Core[] \as R; \normalize R.id L.value; }
```

```toml file=extra/ref.toml
[package]
name = "extra"
```

```ref file=extra/src/root.ref
\module Core { \inductive Unit: \Set := | unit: Unit; }
```

```toml file=other/ref.toml
[package]
name = "other"
[dependencies]
extra = { path = "../extra" }
right = { path = "../right" }
left = { path = "../left" }
```

```ref file=other/src/root.ref
\module Main { \import left.Core[] \as L; \import right.Core[] \as R; \normalize R.id L.value; }
```

### 最初の利用側

共通の型を使う関数と値を検査して保存する。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

### 別の利用側

独立した依存を先に読む利用側でも、保存された型と値を再利用して同じ簡約結果になる。

```toml step
id = "other"
entry = "other"
expect = "accept"
cache = "reused"
stdout_same_as = "cold"
```

### 依存順の変更

manifest の依存の記述順を変えても同じ結果を再利用できる。

```toml step
id = "reordered"
entry = "other"
expect = "accept"
cache = "reused"
stdout_same_as = "cold"
```

```toml file=other/ref.toml
[package]
name = "other"
[dependencies]
left = { path = "../left" }
right = { path = "../right" }
extra = { path = "../extra" }
```

### キャッシュ無効

再利用せずに検査しても同じ簡約結果になる。

```toml step
id = "clean"
entry = "other"
expect = "accept"
cache = "unused"
args = ["--no-cache"]
stdout_same_as = "cold"
```

## macro alias と等号移送

macro alias を通した等号移送の証明は、検証結果を復元した後も利用できる。

```toml scenario
id = "transport-macro"
scope = "package"
```

```ref file=src/root.ref
\module T(A: \Set, F: A -> \Set) {
      \macro identity($a, $u) := \transporteq $a \with x: _ => F x \by { base: $u };
    }
    \module M(A: \Set, F: A -> \Set, a: A, u: F a) {
      \definition cast: F a := \idelim a = a \with x: _ => F x \by { base: u, equality: \refl(a) };
      \definition identity: cast = u := self!{a u};
      \use \root.T[A := A, F := F].identity \as self;
    }
    \module N(A: \Set, F: A -> \Set, a: A, u: F a) {
      \import \root.M[A := A, F := F, a := a, u := u] \as M;
      \definition law: M.cast = u := M.identity;
    }
```

### 初回

等号移送が恒等になることを証明できる。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

### 再検査

保存された検証結果を再利用できる。

```toml step
id = "warm"
expect = "accept"
cache = "reused"
```

### 利用側の変更

利用側の定義名を変えても元の証明を使える。

```toml step
id = "edit"
expect = "accept"
```

```ref file=src/root.ref
\module T(A: \Set, F: A -> \Set) {
      \macro identity($a, $u) := \transporteq $a \with x: _ => F x \by { base: $u };
    }
    \module M(A: \Set, F: A -> \Set, a: A, u: F a) {
      \definition cast: F a := \idelim a = a \with x: _ => F x \by { base: u, equality: \refl(a) };
      \definition identity: cast = u := self!{a u};
      \use \root.T[A := A, F := F].identity \as self;
    }
    \module N(A: \Set, F: A -> \Set, a: A, u: F a) {
      \import \root.M[A := A, F := F, a := a, u := u] \as M;
      \definition law2: M.cast = u := M.identity;
    }
```

### キャッシュ無効

キャッシュを使わなくても同じ結果になる。

```toml step
id = "clean"
expect = "accept"
cache = "unused"
args = ["--no-cache"]
stdout_same_as = "edit"
```

## package の既定のキャッシュ

package の既定のキャッシュは起動する作業ディレクトリを変更しても再利用される。

```toml scenario
id = "default-package-cache"
scope = "package"
cache_dir = "default"
```

```ref file=src/root.ref
\module Main { \definition P: \Prop := \forall (P: \Prop) -> P -> P; \infer P; }
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

入力 package のキャッシュを再利用する。

```toml step
id = "other-cwd"
expect = "accept"
cache = "reused"
cwd = "elsewhere"
stdout_same_as = "cold"
```

