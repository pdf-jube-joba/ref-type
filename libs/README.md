# ライブラリ

各パッケージの [ref.toml](std/ref.toml) が依存先、`src/root.ref` が公開 module を定める。

| パッケージ | 内容 | 直接依存 |
| --- | --- | --- |
| [std](std/README.md) | 論理、データ、整数・有理数、商、代数構造 | なし |
| [real](real/README.md) | 実数の構成・完備性、演算・距離・数列 | std |
| [complex](complex/README.md) | 実数対による複素数と体の構造 | std, real |
| [linear_algebra](linear_algebra/README.md) | 体上の線形代数、実数・複素数への具体化 | std, real, complex |
| [topology](topology/src/root.ref) | 位相空間、距離空間、積・部分空間・距離化 | std, real |
| [calculus](calculus/README.md) | 実数関数の極限、一変数・多変数の微分 | std, real |
| [integration](integration/README.md) | リーマン積分、\(L^1\) 完備化によるルベーグ積分 | std, real |
| [category](category/README.md) | 圏、関手、自然変換、普遍性、随伴、Kan 拡張 | std |

共通の数値的な補題は `real.Analysis` に置き、微分・積分・位相・線形代数が利用する。
`Def` / `Prop` は演算と法則を分けた module、単独の関心ごとは `Distance` / `Sequence` などの名前で公開する。
証明の等式連鎖には [eq_reason!](std/README.md#等式と合同則) を使える。

## 型検査

リポジトリのルートで実行する。

```sh
cargo build -p cli
for package in std real complex linear_algebra topology calculus integration category; do
  target/debug/cli "libs/$package" --no-cache || exit 1
done
target/debug/cli tests/projects/library --no-cache
target/debug/cli tests/projects/category --no-cache
```

[library project](../tests/projects/library/src/root.ref) は分野間の接続と具体例、[category project](../tests/projects/category/src/root.ref) は圏論の利用例を検査する。
処理系のテストとキャッシュの指定は [利用方法](../src/USAGE.md) を参照。
