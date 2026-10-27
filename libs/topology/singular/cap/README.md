# 特異鎖の cap 積

`singular_cap` は整数係数の特異鎖上の cap 積と、その相対版を提供する。`Integral[A, source].At[p, q]` の `map beta` は \((p+q)\)-鎖から \(p\)-鎖への線形写像で、単体の前半を出力し後半に余鎖 `beta` を評価する。`onGenerator` が生成元上の値、`Adjunction.law` が cup 積との評価の随伴を与える。

`Integral.Diagonal.Boundary.Formula.law` は、この約束のもとで
\[
 (\partial c)\frown\beta=\partial(c\frown\beta)+(-1)^p c\frown\delta\beta
\]
を表す。ここで右辺の出力次数は \(p\) である。`Integral.Natural` は連続写像に関する射影公式を与え、`Integral.Unit` は零次の単位余鎖の作用を扱う。

`Integral.Pair.At.Quotient` は相対鎖への絶対余鎖の作用、`RelativeCochain` は相対余鎖と相対鎖から絶対鎖への作用を構成する。両方の境界公式はそれぞれ `Pair.Boundary.Formula` と `Pair.RelativeCochainBoundary.Formula`、相対 cup との随伴は `Pair.At.Adjunction` にある。閉余鎖による作用は `Pair.CohomologyAction` と `Pair.RelativeCohomologyAction` および対応する零次数のモジュールでホモロジー・余コホモロジーへ降下する。

`CochainPair` は相対余鎖の商表示と部分空間上で消える余鎖の表示を比較し、左右の相対 cup 積とその Leibniz 公式、および任意の可換環係数でのコホモロジーへの降下を与える。`CochainPair.Comparison.Cohomology` は相対類から絶対類への写像である。`RelativeEvaluation.With` は任意の整数加群係数で相対 Kronecker 評価を構成する。`External` は絶対外部 cup 積を、`Triple` は二つの部分空間それぞれを保つ鎖・余鎖とコホモロジー上の演算を提供する。

点空間の単位の利用例は [examples/cap](../../examples/cap) にある。個別の通常検査は例えば次で実行できる。

```sh
target/debug/cli libs/topology/singular/cap --module singular_cap.Integral.Pair.At.Adjunction --cache-stats --diagnostics compact
```
