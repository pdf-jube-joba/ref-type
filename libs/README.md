# ライブラリ

各パッケージの `src/root.ref` は公開モジュールの一覧、`tests/projects/library/src/root.ref` と `tests/projects/category/src/root.ref` は利用例を兼ねたライブラリの型検査である。
現在の処理系には任意の証明を通す `admit` / `sorry` はない。
処理系が持つ組み込み公理は、必要な前提を検査する `\axiom:setext`、`\axiom:funext`、`\axiom:classicalIndefiniteChoice` の3つである。
集合の外延性、対応宣言の関数の外延性、古典論理の選択に、それぞれの公理を使う。

## 責務と依存関係

| パッケージ | 責務 | 直接依存 |
| --- | --- | --- |
| [std](std/README.md) | 論理、基本データ、自然数・整数・有理数、商、汎用代数構造 | なし |
| [real](real/README.md) | 実数の構成と完備性、実数上の演算・距離・評価・数列 | std |
| [complex](complex/README.md) | 実数対による複素数、複素演算、共役、複素数の体 | std, real |
| [linear_algebra](linear_algebra/README.md) | 任意の体上の線形代数、実数・複素数への具体化 | std, real, complex |
| topology | 位相空間、抽象的な距離空間、積・部分空間・距離化 | std, real |
| [calculus](calculus/README.md) | 実数関数の極限、一変数・多変数の微分 | std, real |
| [integration](integration/README.md) | タグ付き分割、リーマン積分、\(L^1\) 完備化とルベーグ積分 | std, real |
| [category](category/README.md) | 圏、関手、自然変換、普遍性、随伴、Kan 拡張 | std |

この表は各 `ref.toml` の直接依存を示す。
共通の数値的な補題は `real.Analysis` にあり、微分や積分から位相空間のパッケージを経由する必要はない。
`topology.RealMetric` は `real.Analysis.Distance` の数値距離と法則を `MetricSpace.Metric` にまとめる。
`linear_algebra.Real` は `real.Analysis.Algebra.field` を使って一般の体上の線形代数を具体化する。

## モジュールの分け方

各パッケージの `root.ref` は入口を宣言し、子モジュールは親のスコープを引き継ぐ。
演算と証明を独立して利用するまとまりには `Def` / `Prop` を置き、単独の関心ごとを扱う `Distance` / `Sequence` などはその名前のモジュールで公開する。
型を共有する子から同じ依存を import し直す必要はない。

整数の群完成では、形式差とその演算・同値関係を `Arithmetic.Int.Math` が担当し、同値類と演算の持ち上げは `Set.Quotient` に委ねる。
複素数の成分の計算では、実数の汎用的な恒等式を `real.Analysis.Algebra`、複素乗法の実部・虚部の組み合わせを `Complex.Multiplication` が担当する。
具体化した定理名は再利用の入口として残し、重複する証明本体を共有する。
[移動した公開定理の対応表](real/README.md#移動した公開定理)に import の変更先を記載している。

## 証明の書き方

仮定と中間結果は `\block` の `\fun` / `\let`、消去則に続く証明は `\enough` で順に並べる。
例えば `Analysis.Sequence.limitUnique` は、`\enough _ \by { E.separatedBySmall u v } \then` に続けて誤差と正値性を導入し、二つの列の評価を `nearU` / `nearV` に分ける。
等式を順につなぐときは [標準ライブラリの `eq_reason!`](std/README.md#等式と合同則) を使う。
分岐ごとに長い計算を繰り返す場合は、`CauchyReal.Sequences.reciprocalMulEquivalent` の `productOne` のように局所補題へまとめる。
型の注釈は期待型から分かる箇所で `_` を使い、大きな有理数の証明では中間項の値を明示して推論の負荷を抑える。

## 型検査

```sh
cargo build --bin cli
for package in std real complex linear_algebra topology calculus integration category; do
  target/debug/cli "libs/$package" --no-cache || exit 1
done
target/debug/cli tests/projects/library --no-cache
target/debug/cli tests/projects/category --no-cache
cargo test --workspace
```

ライブラリの検査は一つずつ実行し、`--no-cache` でソース全体を検証する。
`tests/projects/library` は分野間の接続と具体例、`tests/projects/category` は圏論の利用例を確認する。
`cargo test --workspace` は処理系の unit test、`.ref` の成功・失敗テスト、doc test を実行する。
