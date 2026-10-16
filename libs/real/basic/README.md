# 実解析の基礎

構成済みの実数の演算、距離評価、数列、平方根、有限和を扱う。

| module | 内容 |
| --- | --- |
| [Analysis](src/Analysis.ref) | 構成済みの Dedekind 実数の型と演算 |
| `Analysis.Algebra` | 算術の恒等式、平方の非負性、`Field` 構造 |
| `Analysis.Distance` | 有理数の埋め込み、最大・最小、距離の法則 |
| `Analysis.Estimates` | 重み付き距離、中点、微小な誤差による順序・等式の判定 |
| `Analysis.Sequence` | 実数列の Cauchy 条件、収束、極限の構成と一意性 |
| `Analysis.SquareRoot` | 上限からの平方根の構成、非負性・平方・一意性、平方根の距離評価 |
| `Analysis.Estimates.Product` / `Analysis.Inverse` | 積と逆数の距離評価、正負の領域での逆数の制御 |

`metric_spaces.RealMetric` が距離空間、`linear_algebra.Real` がベクトル空間への接続を提供する。

```text
\import real.Analysis[] \as R;
\import R.Distance[] \as Distance;
\definition selfDistance: \forall (x: R.Real) -> R.distance x x = R.zero :=
  Distance.distanceSelf;
```

[利用例](../../../libs/analysis/scalar_compatibility/src/Compatibility.ref) は定数列の極限と他分野との演算の共有を検査する。
