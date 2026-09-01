## フォルダ構成
- kernel: ほぼ理論通りの実装
  - 理論側の言語
  - type-check / type-infer
  - checker
- front: 言語処理系
  - 実装側の言語
  - parser
  - elaboration

## ソースファイルと module

ソースファイルの拡張子は `.ref`。CLI にはルートファイルを一つ渡す。

```sh
cargo run -- file path/to/root.ref
```

typing rule の呼び出しを木構造で確認する場合は `--trace` を付ける。

```sh
cargo run -- file path/to/root.ref --trace
```

typing は通常の `tracing` span/event として記録される。ログレベルを細かく指定する
場合は、たとえば `RUST_LOG=ref_type::typing=debug` を利用できる。通常実行では
typing span は無効で、型検査に必要な証明は各項の部分項として検査される。

本体を別ファイルに置く module は `\module Name;` と宣言する。ルートファイルと
同じディレクトリの `Name.ref` が module 本体として読み込まれる。外部ファイルには
`\module Name { ... }` を繰り返さず、module item を直接記述する。

子 module の配置は論理 module パスに対応する。たとえば `root.ref` の
`\module Algebra;` は `Algebra.ref`、その中の `\module Group;` は
`Algebra/Group.ref` を読み込む。ファイル名の大文字と小文字は宣言と一致させる。

## 公理

kernel が提供する公理は proof term として使う。各引数は通常の typing rule で検査される。

```text
\axiom:setext(A, B, forward, backward)
\axiom:funext(f, g, pointwise)
\axiom:classicalIndefiniteChoice(X, Family, inhabited)
```

`setext` は同じ `Power(X)` の要素と双方向の包含証明を、`funext` は同じ関数型の
二項と各点での等号を要求する。`classicalIndefiniteChoice` は `Family: X -> Set` と
`(x: X) -> exists (Family x)` から `exists ((x: X) -> Family x)` を返す。
