# 実数

Dedekind 実数は inhabited・proper・lower・rounded・located な切断として定義される。
`DedekindReal.Cuts.Def` は切断の候補となる lower set、`Cuts.Prop` はそれらが切断になる証明を公開する。
`DedekindReal.Arithmetic.Def` は切断上の演算、`Arithmetic.Prop` は算術法則を公開する。
`DedekindReal.Field.Def` は演算と法則を公理的実数の構造へまとめる。

Cauchy 実数は有理数列を「差が零へ収束する」関係で割った商である。
`CauchyReal.Quotient.Sequences.Def` は列上の演算、`Classes.Def` は同値類上の演算を構成する。
`CauchyReal.Quotient.Arithmetic.Def` と `Arithmetic.Prop` は商上の算術、`Inverse.Def` と `Inverse.Prop` は逆数の構成と性質を公開する。
順序と完備性はそれぞれ `CauchyReal.Order` と `CauchyReal.Completeness` にある。

## 具体的な実数上の共通ライブラリ

`Analysis` は Dedekind 実数上の演算と解析をまとめる。
`CauchyReal` が有理数列から実数自体を構成するのに対し、`Analysis.Sequence` は構成済みの Dedekind 実数の列を扱う。
パッケージの依存は `std` だけである。

| モジュール | 責務 |
| --- | --- |
| `Analysis` | 実数の型、符号付きの演算、半分、二点の中点、数値としての距離 |
| `Analysis.Algebra` | 加減乗算の恒等式、平方の非負性、標準の `Field` 構造 |
| `Analysis.Distance` | 有理数の埋め込みと順序、最大・最小、距離とその法則 |
| `Analysis.Estimates` | 重み付き距離、中点、微小な誤差による順序・等式の判定 |
| `Analysis.Sequence` | 実数列の Cauchy 条件、収束、完備性による極限の構成と一意性 |

`Algebra` → `Distance` → `Estimates` → `Sequence` の順に下位の結果を使う。
ここで矢印は結果を提供する側から利用する側へ向く。
実数値の距離を抽象的な距離空間にまとめるのは `topology.RealMetric.metric`、ベクトル空間への具体化は `linear_algebra.Real` が担当する。

```text
\import real.Analysis[] \as R;
\import R.Algebra[] \as Algebra;
\import R.Distance[] \as Distance;
\import R.Sequence[] \as Sequence;
\import std.Data[].Nat[] \as N;

\definition selfDistance: \forall (x: R.Real) -> R.distance x x = R.zero :=
  Distance.distanceSelf;
\definition uniqueLimit: \forall (s: N.Nat^ -> R.Real) -> \forall (u, v: R.Real) ->
  Sequence.Converges s u -> Sequence.Converges s v -> u = v :=
  Sequence.limitUnique;
```

[実行される利用例](../../tests/projects/library/src/AnalysisExamples.ref)は、定数列の極限と、距離空間・線形代数との演算の共有を確認する。

## 移動した公開定理

| 旧モジュール | 現在のモジュール |
| --- | --- |
| `topology.RealMetric` の数値演算・補題 | `real.Analysis.Distance`（`metric` は `topology.RealMetric`） |
| `integration.Real.Estimates` | `real.Analysis.Estimates` |
| `integration.Real.Sequence` | `real.Analysis.Sequence` |
| `complex.Complex.Scalar` の実数の恒等式・平方の補題 | `real.Analysis.Algebra` |
| `complex.Complex.Scalar.assocRealPart` / `assocImaginaryPart` | `complex.Complex.Multiplication` |

移動した定理の名前と数学的な主張は維持し、import の所有パッケージを変更している。
旧 `Complex.Scalar` の `zero`・`one`・`add`・`neg`・`sub`・`mul` は `real.Analysis` にある。
`Estimates.mulSub`・`subAdd`・`addShuffle` と `Distance.leAddOfNonnegative` は、共通の `Algebra` の証明を再利用する。

```sh
cargo run --quiet --bin cli -- libs/real --no-cache
```
