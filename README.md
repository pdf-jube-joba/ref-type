# このリポジトリについて
proof checker を作る。 **コンパイルすることは忘れて** 単に形式的な記述をチェックするための言語を作る。

# 構成
- doc/ はドキュメント置き場
    - doc/book/ に考えている体系についての文章を書く
- formalization/ は他の定理証明支援系で現在の体系の性質を証明する
- src/ は実装
    - src/core/ はライブラリとしてのコア部分
    - src/terminal/ は CUI 用のプログラム
    - src/USAGE.md は CUI の使い方

# ソースファイルと module

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
