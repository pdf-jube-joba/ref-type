# 実数

`std` に依存し、Dedekind 切断と有理数 Cauchy 列の商による二つの実数構成を提供する。

| module | 内容 |
| --- | --- |
| [DedekindReal](src/DedekindReal.ref) | 切断、算術、順序、完備性、体の構造 |
| [CauchyReal](src/CauchyReal.ref) | 有理数列、商、算術・逆数、順序、完備性 |
| [Analysis](src/Analysis.ref) | 構成済みの Dedekind 実数の型と演算 |
| `Analysis.Algebra` | 算術の恒等式、平方の非負性、`Field` 構造 |
| `Analysis.Distance` | 有理数の埋め込み、最大・最小、距離の法則 |
| `Analysis.Estimates` | 重み付き距離、中点、微小な誤差による順序・等式の判定 |
| `Analysis.Sequence` | 実数列の Cauchy 条件、収束、極限の構成と一意性 |

`topology.RealMetric` が距離空間、`linear_algebra.Real` がベクトル空間への接続を提供する。

```text
\import real.Analysis[] \as R;
\import R.Distance[] \as Distance;
\definition selfDistance: \forall (x: R.Real) -> R.distance x x = R.zero :=
  Distance.distanceSelf;
```

[利用例](../../tests/projects/library/src/AnalysisExamples.ref) は定数列の極限と他分野との演算の共有を検査する。
検査方法は [ライブラリ一覧](../README.md#型検査) を参照。
