# 複素数

Dedekind 実数の対として \(\mathbb{C}=\mathbb{R}\times\mathbb{R}\) を構成する。
実数の乗法と逆数には `real.DedekindReal.Arithmetic.Prop` の符号付き演算を使う。

| モジュール | 内容 |
| --- | --- |
| `Complex` | `Real`、`Complex`、構築関数 `make`、実部 `re`、虚部 `im` |
| `Complex.Def` | `zero`、`one`、`i`、実数の埋め込み、四則演算、実数倍、共役、絶対値の二乗 |
| `Complex.Multiplication` | 複素乗法の結合則に使う実部・虚部の計算 |
| `Complex.Prop` | 外延性、埋め込みの単射性と演算保存、算術法則、共役、絶対値の二乗、逆数と除法の法則 |
| `Complex.Algebra` | 加法可換群、可換環、体の構造 |

実数の恒等式と平方の性質は `real.Analysis.Algebra` を使う。

`make a b` は \(a+bi\) を表す。
共役と絶対値の二乗、逆数は次の式で定義する。

\[
\overline{a+bi}=a-bi,\qquad
\operatorname{normSq}(a+bi)=a^2+b^2,\qquad
(a+bi)^{-1}=\frac{a-bi}{a^2+b^2}.
\]

零の逆数と零による除法は零とする。

[利用例](../../tests/projects/library/src/ComplexExamples.ref) は演算・共役・体の構造を検査する。

検査方法は [ライブラリ一覧](../README.md#型検査) を参照。
