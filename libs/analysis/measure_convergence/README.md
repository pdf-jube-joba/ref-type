# 測度積分の収束

`measure_convergence.On[A, mu]` は `functional_analysis.Measure` の測度と単関数積分に基づく収束定理を提供する。
実数の積分は、可測で絶対値の下積分が有限な関数について構成される。

```ref
\import measure_convergence.On[A := A, mu := mu] \as Integration;
\import functional_analysis.Measure[A := A].Integral[mu := mu] \as RealIntegral;

\definition addExample: \forall (f, g: RealIntegral.Representatives) ->
  RealIntegral.integral (Integration.Linear.addRepresentative f g) =
    Real.add (RealIntegral.integral f) (RealIntegral.integral g) := Integration.integralAdd;
```

`monotone` は可測な増加実関数列の各点上限に対する下積分の単調収束を示す。
`FatouFor[f].inequality` は非負可測関数列について、末尾下限の下積分からなる上極限を積分値の下極限で評価する。
有限の各点下極限が存在する場合、`finiteLiminf` と `finiteInequality` はその関数の下積分について述べる。
`NonnegativeAdd[p, q].lowerIntegralAdd` は非負可測関数の下積分の加法性を示す。

`Dominated[d]` は、可積分関数列が一つの可積分関数に絶対値で支配され、各点で収束する場合に、極限の可積分性と積分列の収束を導く。
`AEDominated[d]` は収束と支配が可測零集合の外で成り立つ場合を扱い、極限と a.e. 一致する可積分代表を構成する。
元の極限が可測なら `limitIntegrable` により元の関数も可積分である。
可測性を仮定しない場合に代表を返すのは、完備でない測度空間では零集合の部分集合が可測とは限らないためである。

`IntegralClasses` と `integral` は a.e. 同値類とその積分を表す。
`addClasses`、`scaleClass`、`integralClassAdd`、`integralClassScalar` は商上の演算と積分の線形性を提供する。
代表元については `integralAdd`、`integralScalar`、`integralNeg`、`integralMono`、`integralAbsBound` を使える。

`Series[terms].Exchange` は可積分関数列の部分和が一つの可積分関数で支配され、各点で収束する場合、積分と級数を交換する。
`Series[terms].AEExchange` は同じ条件が可測零集合の外で成り立つ場合に、極限の可積分代表と交換則を提供する。
どちらも部分和の積分が各項の積分の部分和であることを証明している。

`Complex` は実部・虚部を、`Vector[n]` は有限個の実座標をそれぞれ積分する。
加法、スカラー倍、a.e. 不変性、成分ごとの優収束と級数交換を提供し、複素積分では複素スカラー倍も扱う。
`Complex.integralNormBound` は複素積分の絶対値を実部と虚部の絶対値積分の和で評価し、`Vector[n].integralL1Bound` は座標の ℓ¹ ノルムを各座標の絶対値積分の和で評価する。
これらは成分ごとの評価であり、右辺をベクトル値関数のノルムの積分に置き換える主張ではない。

`On.Examples` には零関数の積分、商上の加法、零列の優収束と級数交換の利用例がある。
