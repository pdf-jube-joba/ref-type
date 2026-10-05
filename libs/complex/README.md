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

`normSqNonnegative`、`normSqZero`、`normSqPositive` はそれぞれ絶対値の二乗の非負性、零ならば元も零であること、非零の元では正であることを証明する。
`normSqMul` は積の絶対値の二乗が各絶対値の二乗の積になることを証明する。
`inverseNonzero` は非零の元について逆数との積が一になることを示し、`Algebra.field` はこれを既存の `Alg.Field` にまとめる。
零の逆数と零による除法は零とする。

```text
\import complex.Complex[] \as C;
\import C.Def[] \as D;
\import C.Prop[] \as Laws;
\import C.Algebra[] \as Algebra;

\definition imaginarySquare: D.mul D.i D.i = D.neg D.one := Laws.iSquared;
\definition quotient: D.div D.i D.i = D.one := Laws.divSelf D.i Laws.iNonzero;
```

[利用例](../../tests/projects/library/src/ComplexExamples.ref)は \((1+i)^2=2i\)、\((1+i)\overline{(1+i)}=2\)、\(i/i=1\)、零による除法と体の構造からの法則の取り出しを検査する。

```sh
cargo run --quiet --bin cli -- libs/complex
cargo run --quiet --bin cli -- tests/projects/library
```
