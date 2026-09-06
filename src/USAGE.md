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
cargo run -- path/to/root.ref
```

typing rule の呼び出しを木構造で確認する場合は `--trace` を付ける。

```sh
cargo run -- path/to/root.ref --trace
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

## Program の値束縛

`let^v` は型注釈を含む `\vlet(x, A, value, body)` と書く。`A` は
`ValueType` で、`value` がその型を持つことを検査する。`x` は `body` 内だけで
有効であり、型注釈と右辺は外側のスコープで解釈する。

```text
\module Example(A: \VType, a: A) {
  \cdefinition result: \F(A) := \vlet(x, A, a, \return(x));
}
```

旧構文 `\vlet(x, value, body)` は受け付けない。注釈位置の `_` は他の型注釈と
同様に制約から補完し、解決できなければエラーになる。

## 実行速度の計測

```sh
cargo bench -p cli --bench performance -- --save-baseline before
# 実装を変更した後
cargo bench -p cli --bench performance -- --baseline before --save-baseline after
```

構文解析・型検査・正規化・Program 評価を計測します。
対象の絞り込みや結果の見方は [ベンチマークの手順](cli/benches/README.md) を参照してください。

## 実行と診断

```sh
cargo run -p cli -- lib/root.ref
cargo run -p cli -- lib/root.ref --trace
RUST_LOG=ref_type=trace cargo run -p cli -- lib/root.ref
```

`--trace` は Set/Prop・Program の型検査、定義登録、反映、正規化・評価のログを木構造で表示します。
`RUST_LOG=ref_type=trace` では束縛の出入りと簡約ステップも表示します。
特定の処理だけを追う場合は `RUST_LOG=ref_type::typing::program=debug` や
`RUST_LOG=ref_type::reduction=trace` を指定できます。`RUST_LOG` は `--trace` の既定フィルタより優先されます。
ログとエラーは標準エラー出力へ書き込みます。ファイルへ保存する場合は `2> kernel.log` を付けます。

未解決ゴールには文脈・要求される型・制約を表示します。ファイルから読み込んだ宣言のエラーには
元ファイル・行・列とソースの抜粋を付けます。型検査の位置表示は宣言単位、構文エラーはトークン単位です。
外部モジュールのパラメータは宣言元ファイル、本文は外部ファイルの位置を使います。

`CrateEnv::add_definition` は型検査に成功した定義だけを登録し、`Result<DefId, String>` を返します。
Program 定義では本体と、指定された反映証明の型を検査します。
モジュール実体化でも同じ登録 API を使い、実体化時の検証済み文脈を保持します。

```sh
cargo test --workspace --offline
```

`tests/ng` の各ファイルには `/* expect-error: 診断に含まれる文字列 */` を書きます。
複数指定した場合はすべて照合します。終了コード 1 と診断を確認し、panic やシグナル終了は失敗として扱います。
