# cli / checking

## 具体化した module 内の inspection hole

恒等写像で具体化した入れ子の module を import した文脈で、inspection hole を含む宣言と独立した型エラーを比較する。

```toml scenario
id = "instantiated-hole-diagnostics"
scope = "package"
```

```ref file=src/root.ref
\module Family(A, C: \Set, F: A -> C) {
  \module Along(B: \Set, K: A -> B) {
    \definition Carrier: \Set := C;
  }
}
\module Reproduction(A, C: \Set, F: A -> C) {
  \import \root.Family[A := A, C := C, F := F].Along[B := A,
    K := \fun (x: A) => x] \as Extension;
  \definition Carrier: \Set := Extension.Carrier;
  \definition pending: \Prop := ?;
}
\module Independent {
  \definition bad: \Prop := \Set;
}
```

### 詳細な診断

inspection hole と型エラーを含む。

```toml step
id = "detailed"
expect = "reject"
args = ["--diagnostics", "detailed"]
```

### 簡潔な診断

同じ入力は簡潔な診断方式でも拒否される。

```toml step
id = "compact"
expect = "reject"
args = ["--diagnostics", "compact"]
```

### 宣言の修正

hole と型エラーを修正すると、module の具体化と import を含めて受理される。

```toml step
id = "fixed"
expect = "accept"
```

```ref file=src/root.ref
\module Family(A, C: \Set, F: A -> C) {
  \module Along(B: \Set, K: A -> B) {
    \definition Carrier: \Set := C;
  }
}
\module Reproduction(A, C: \Set, F: A -> C) {
  \import \root.Family[A := A, C := C, F := F].Along[B := A,
    K := \fun (x: A) => x] \as Extension;
  \definition Carrier: \Set := Extension.Carrier;
  \definition pending: \Prop := \forall (P: \Prop) -> P -> P;
}
\module Independent {
  \definition good: \Prop := \forall (P: \Prop) -> P -> P;
}
```

## 構文エラー後の独立した query

詳細な検査では独立した module の query を実行できる。
簡潔な診断方式では最初の構文エラーで停止する。

```toml scenario
id = "parse-error-recovery"
scope = "package"
entry = "src/root.ref"
```

```ref file=src/root.ref
\module Broken;
\module Good;
```

```ref file=src/Broken.ref
\definition bad: \Prop := ;
```

```ref file=src/Good.ref
\infer \Set;
```

### 詳細な検査

入力は拒否されるが、独立した query の結果は標準出力に返る。

```toml step
id = "detailed"
expect = "reject"
args = ["--diagnostics", "detailed"]
stdout_lines = 1
```

### 簡潔な検査

最初の構文エラーで停止し、後続の query を実行しない。

```toml step
id = "compact"
expect = "reject"
args = ["--diagnostics", "compact"]
stdout = ""
```

## module の検査範囲

選択した module と子 module を検査し、無関係な module の型エラーは検査対象に含めない。

```toml scenario
id = "module-selection"
scope = "package"
```

```ref file=src/root.ref
\module Good { \definition identity(A: \Set)(x: A): A := x; }
        \module Bad { \module Child { \definition invalid: \Set := \Prop; } }
```

### 正常な範囲

Good の宣言は型が合う。

```toml step
id = "good"
expect = "accept"
args = ["--module", "test.Good"]
```

### 子 module の型エラー

Bad の子 module に型エラーがある。

```toml step
id = "bad"
expect = "reject"
args = ["--module", "test.Bad"]
```

### 存在しない module

選択した module が存在しない。

```toml step
id = "missing"
expect = "reject"
args = ["--module", "test.Missing"]
```

## 親自身と子の検査

親自身の検査と子を含む検査では検査範囲が異なる。
子が依存する親の宣言は、子だけを選択しても検査する。

```toml scenario
id = "module-only"
scope = "package"
```

```ref file=src/root.ref
\module M {
      \definition P: \Prop := \forall (P: \Prop) -> P;
      \module Good { \definition Q: \Prop := \forall (P: \Prop) -> P; }
      \module Bad { \definition wrong: \Set := \Set; }
    }
```

### 一覧

ソースにある親と子を列挙できる。

```toml step
id = "list"
expect = "accept"
args = ["--list-modules"]
stdout = "test\ntest.M\ntest.M.Good\ntest.M.Bad\n"
```

### 親自身

親自身の宣言に型エラーがない。

```toml step
id = "parent"
expect = "accept"
args = ["--module", "test.M", "--module-only"]
```

### 子も検査

子の宣言に型エラーがある。

```toml step
id = "whole"
expect = "reject"
args = ["--module", "test.M"]
```

### 親への依存

子が参照する親の宣言が型を持たない。

```toml step
id = "dependency"
expect = "reject"
args = ["--module", "test.M.Child", "--module-only"]
```

```ref file=src/root.ref
\module M { \definition wrong: \Set := \Set; \module Child { \definition T: \Set := \super.wrong; } }
```

## 構文と型の検査

構文が正しくても型が合わない入力と、構文自体が成立しない入力を比較する。

```toml scenario
id = "parse-and-check"
scope = "package"
```

```ref file=src/root.ref
\module Root { \definition invalid: \Prop := \Set; }
```

### 構文だけ

構文が正しい。

```toml step
id = "parse"
expect = "accept"
args = ["--parse-only"]
stdout = ""
stderr_empty = true
```

### 型も検査

宣言された型と本体の型が異なる。

```toml step
id = "check"
expect = "reject"
```

### 構文の欠落

definition の本体が欠けている。

```toml step
id = "syntax"
expect = "reject"
args = ["--parse-only"]
```

```ref file=src/root.ref
\module Root { \definition invalid: \Prop := ; }
```

## 外部 module の構文検査

構文が正しくても型が合わない入力と、構文自体が成立しない入力を比較する。

```toml scenario
id = "parse-external-modules"
scope = "package"
```

```ref file=src/root.ref
\module Child;
```

```ref file=src/Child.ref
\definition invalid: \Prop := \Set;
```

### 構文だけ

構文が正しい。

```toml step
id = "parse"
expect = "accept"
args = ["--parse-only"]
stdout = ""
stderr_empty = true
```

### 型も検査

宣言された型と本体の型が異なる。

```toml step
id = "check"
expect = "reject"
```

### 構文の欠落

definition の本体が欠けている。

```toml step
id = "syntax"
expect = "reject"
args = ["--parse-only"]
```

```ref file=src/root.ref
\module Child;
```

```ref file=src/Child.ref
\definition invalid: \Prop := ;
```

## 外部 module の拒否

日本語のコメントを含む外部 module の型エラーと構文エラーを検査する。

```toml scenario
id = "external-errors"
scope = "package"
```

```ref file=src/root.ref
\module Child;
```

```ref file=src/Child.ref
/* 日本語 */
\definition bad: \Prop := \Set;
```

### 型

集合を命題として定義している。

```toml step
id = "type"
expect = "reject"
stdout = ""
stderr_empty = false
```

### 構文

definition の本体が欠けている。

```toml step
id = "syntax"
expect = "reject"
```

```ref file=src/Child.ref
\definition bad: \Prop := ;
```

## 診断方式と環境変数

診断の方式とその指定方法によらず、同じ不正な宣言を拒否する。

```toml scenario
id = "diagnostic-modes"
scope = "package"
```

```ref file=src/root.ref
\module Child;
```

```ref file=src/Child.ref
\definition bad: \Prop := \Set;
```

### 既定

不正な型の宣言を拒否する。

```toml step
id = "default"
expect = "reject"
```

### 環境変数

環境変数で簡潔な診断方式を選べる。

```toml step
id = "environment"
expect = "reject"
env = { "REF_TYPE_COMPACT_DIAGNOSTICS" = "1" }
```

### CLI による指定

環境変数と CLI の方式が異なっても合否は変わらない。

```toml step
id = "detailed"
expect = "reject"
args = ["--diagnostics", "detailed"]
env = { "REF_TYPE_COMPACT_DIAGNOSTICS" = "1" }
```

### 簡潔な方式

CLI で簡潔な診断方式を指定しても拒否される。

```toml step
id = "compact"
expect = "reject"
args = ["--diagnostics", "compact"]
env = { "REF_TYPE_COMPACT_DIAGNOSTICS" = "0" }
```

## contextual unsolved goal

inspection hole は解が求まっていても確認を要求するため、診断方式によらず拒否される。

```toml scenario
id = "diagnostics-contextual_unsolved_goal"
scope = "package"
```

```ref file=src/root.ref
\module ContextualUnsolvedGoal(A: \Set(0)) {
  /* The reported goal should retain x in its local context. */
  \definition pending: A -> A := \fun (x: A) => ?;
}
```

### 通常

inspection hole が残る。

```toml step
id = "normal"
expect = "reject"
```

### 簡潔

簡潔な診断方式でも拒否される。

```toml step
id = "compact"
expect = "reject"
args = ["--diagnostics", "compact"]
```

## solved inspection program

inspection hole は解が求まっていても確認を要求するため、診断方式によらず拒否される。

```toml scenario
id = "diagnostics-solved_inspection_program"
scope = "package"
```

```ref file=src/root.ref
\module Inspection(A: \VType, a: A) {
  \inductive Box[X: \VType]: \VType := | box: X -> Box;
  \definition pending: Box[A] := Box[?]::box a;
}
```

### 通常

inspection hole が残る。

```toml step
id = "normal"
expect = "reject"
```

### 簡潔

簡潔な診断方式でも拒否される。

```toml step
id = "compact"
expect = "reject"
args = ["--diagnostics", "compact"]
```

