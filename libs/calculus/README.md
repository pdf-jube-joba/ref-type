# 微分

Dedekind 実数上の関数の極限と微分を扱う。
実数の演算には `real.DedekindReal.Arithmetic.Prop` の符号付きの乗法・逆数を使い、距離には `topology.RealMetric` を使う。

| モジュール | 内容 |
| --- | --- |
| `Real` | 実数の型と演算、定数関数、恒等関数、一次関数 |
| `Real.Limit.Def` | ε–δ 極限 `HasLimitAt` と半径の条件 `Control` |
| `Real.Limit.Prop` | 定数・恒等関数の極限、点を除いた関数の一致による極限の移送 |
| `Real.Derivative.Def` | 差商 `slope`、微分 `HasDerivativeAt`、微分可能性、導関数付きの関数 |
| `Real.Derivative.Prop` | 定数・恒等関数・一次関数の微分則と微分可能な関数の構成 |
| `Real.Multivariable[n].Space.Def` | \(\mathbb{R}^n\) の座標、座標の置換、最大値ノルムと連続性 |
| `Real.Multivariable[n].Partial.Def` | 偏微分、勾配、二階混合偏微分の交換可能性 |
| `Real.Multivariable[n].Differential.Def` | 線形写像、全微分と全微分可能性 |
| `Real.Multivariable[n].Directional.Def` | 開区間上の曲線に沿う方向微分、接ベクトルと一致の条件 |
| `Real.Multivariable[n].Smooth.Def` | 反復偏導関数、\(C^k\) 級、\(C^\infty\) 級と微分順序の交換可能性 |

`HasLimitAt f a l` は、任意の \(\varepsilon>0\) に対して \(\delta>0\) が存在し、\(x\ne a\) かつ \(d(x,a)<\delta\) ならば \(d(f(x),l)<\varepsilon\) が成り立つことを表す。
`HasDerivativeAt f a m` は、差商 \[ \frac{f(x)-f(a)}{x-a} \] の \(x\to a\) における極限が \(m\) であることを表す。

微分則は、定数関数の導関数が零、恒等関数の導関数が一、一次関数 \(x\mapsto mx+b\) の導関数が \(m\) であることを証明する。

```text
\import calculus.Real[] \as C;
\import C.Derivative[].Def[] \as D;
\import C.Derivative[].Prop[] \as Laws;

\definition affineDerivative: \forall (m, b, a: C.Real) ->
  D.HasDerivativeAt (C.affine m b) a m := Laws.affineDerivative;

\definition affineFunction(m, b: C.Real): D.DifferentiableFunction :=
  Laws.affineDifferentiable m b;
```

`DifferentiableAt f a` はその点での微分係数の存在、`HasDerivative f g` はすべての点で \(g(a)\) が微分係数であることを表す。
`DifferentiableFunction` は関数と導関数を持つ `\structure` であり、`differentiable` フィールドが微分則を保持する。

## 多変数関数

`Real.Multivariable[n := n]` は任意の自然数 \(n\) に対する実数値関数 \(f:\mathbb{R}^n\to\mathbb{R}\) を扱う。
`Coordinate` は `Fin n`、`Point` は `Coordinate -> Real`、`Function` は `Point -> Real` である。
ノルムは \(\lVert h\rVert_\infty=\max_i |h_i|\) であり、\(n=0\) では零とする。
`ContinuousAt` はこのノルムに関する ε–δ 連続性であり、`Continuous` はすべての点での連続性を表す。

`Partial.HasPartialDerivativeAt f i a m` は、座標 \(i\) だけを \(t\) に置き換えた関数の \(t=a_i\) における微分係数が \(m\) であることを表す。
`HasPartialDerivative f i g` は偏導関数 \(g\)、`HasGradient f g` は各成分が偏導関数である勾配 \(g:\mathbb{R}^n\to\mathbb{R}^n\) の仕様である。
`MixedPartialsCommuteAt f i j a` は、一階偏導関数と両順序の二階混合偏微分係数が存在し、\(\partial_i\partial_j f(a)=\partial_j\partial_i f(a)\) となることを表す。
`MixedPartialsCommute f` はすべての座標対と点に対する交換可能性である。

`Differential.LinearMap` は写像 \(L:\mathbb{R}^n\to\mathbb{R}\) と加法性・実数倍の保存を持つ。
`HasDifferentialAt f a L` は、任意の \(\varepsilon>0\) に対して \(\delta>0\) が存在し、\(0<\lVert h\rVert_\infty<\delta\) ならば
\[
  |f(a+h)-f(a)-L(h)|<\varepsilon\lVert h\rVert_\infty
\]
が成り立つことを表す。
`DifferentiableAt` は全微分の存在、`HasDifferential` は各点での全微分を指定する。
`DifferentiableFunction` は関数と全微分、`Partial.PartiallyDifferentiableFunction` は関数と勾配を保持する。

`Smooth.PartialFamily` は座標の有限列から反復偏導関数への写像である。
空列は元の関数を表し、列の先頭に座標 \(i\) を追加すると、その列が表す関数をさらに \(i\) で偏微分する。
例えば列 \([i,j]\) は \(\partial_i(\partial_j f)\) を表す。
`PartialFamilyLaws` は \(k\) 階までの微分の仕様、`ContDiffLaws` はその仕様と零階から \(k\) 階までのすべての反復偏導関数の連続性をまとめる。
`ContDiff k f` はそのような族の存在、`Smooth f` はすべての自然数 \(k\) に対する `ContDiff k f` を表す。
`contDiffZero` は \(C^0\) 級と連続性が同値であることを証明する。

`SameMultiIndex` は各座標の出現回数が等しい二つの列を表す。
`CommutingPartialsAt k f a` は \(k\) 階までの反復偏導関数が存在し、同じ出現回数を持つ任意の微分順序で点 \(a\) での値が一致することを表す。
`CommutingPartials k f` はすべての点でのこの性質である。

```text
\import std.Data[].Nat[] \as N;
\import calculus.Real[] \as C;
\import C.Multivariable[n := N.Nat^::succ (N.Nat^::succ N.Nat^::zero)] \as M;
\import M.Space[].Def[] \as Space;
\import M.Partial[].Def[] \as Partial;
\import M.Partial[].Prop[] \as PartialLaws;
\import M.Smooth[].Def[] \as Smooth;
\import M.Smooth[].Prop[] \as SmoothLaws;

\definition projectionPartial: \forall (i: M.Coordinate) ->
  Partial.HasPartialDerivative (Space.projection i) i (Space.constantFunction C.one) :=
  PartialLaws.projectionPartial;

\definition constantSmooth: \forall (c: C.Real) -> Smooth.Smooth (Space.constantFunction c) :=
  SmoothLaws.constantSmooth;
```

各 `Prop` モジュールには、定数関数の偏微分・全微分・混合偏微分の交換可能性・\(C^\infty\) 級と、座標関数の偏微分・全微分の証明がある。

## 曲線に沿う方向微分

`Directional.ParameterInterval` は端点 \(a,b\) と \(a<0<b\) の証明を持ち、`Parameter interval` は開区間 \((a,b)\) の実数である。
`Curve` はこの区間と写像 \(\gamma:(a,b)\to\mathbb{R}^n\) を保持し、`center curve` は \(\gamma(0)\) を表す。
`HasDirectionalDerivativeAlong f curve m` は二側極限
\[
  D_\gamma f=\lim_{t\to0}\frac{f(\gamma(t))-f(\gamma(0))}{t}=m
\]
の存在を表す。
極限の変数は曲線の定義域に属する \(t\) であり、差商の条件には \(t\ne0\) を使う。
`DirectionallyDifferentiableAlong` はこの微分係数の存在を表す。

`HasTangent curve v` はすべての座標で \(\gamma_i'(0)=v_i\) が成り立つこと、`CurveDirection[curve, p, v]` は \(\gamma(0)=p\) と \(\gamma'(0)=v\) を表す。
`HasDirectionalDerivativeAt f p v m` は、この始点と接ベクトルを持つすべての曲線に沿う方向微分が \(m\) となることを表す。
`line interval p v` は \(\gamma(t)=p+tv\) であり、`lineCenter` と `lineTangent` はその始点と接ベクトルを証明する。

二つの曲線 \(\gamma,\eta\) に沿う方向微分が一致する十分条件は、
\[
  \gamma(0)=\eta(0)=p,\qquad \gamma'(0)=\eta'(0)=v,
\]
かつ \(f\) が \(p\) で全微分可能であることである。
このとき合成関数の微分則により
\[
  D_\gamma f=df_p(v)=D_\eta f
\]
となる。
`SameDirection` は共通の始点と接ベクトル、`AgreementConditions` はこの条件に \(f\) の全微分の仕様を加えた record である。
より一般に、共通の始点 \(p\) で \(f\) が全微分可能で、両曲線の接ベクトルが存在するとき、方向微分が一致する必要十分条件は
\[
  df_p(\gamma'(0))=df_p(\eta'(0)),
  \qquad\text{すなわち}\qquad
  df_p(\gamma'(0)-\eta'(0))=0
\]
である。
`DifferentialAgreementConditions` は両接ベクトルと、全微分による像の一致を保持する。
二つの曲線の定義域となる開区間は、それぞれ異なるものを取れる。
接ベクトル \(v\) はパラメータに対する速さを含み、\(\eta(t)=\gamma(ct)\) では \(\eta'(0)=c\gamma'(0)\) と方向微分 \(D_\eta f=cD_\gamma f\) が対応する。
`DirectionalDerivativesAgree` は、両曲線に沿う方向微分が存在して同じ値を持つことを表す。

```text
\import M.Directional[].Def[] \as Directional;
\import M.Directional[].Prop[] \as DirectionalLaws;

\definition projectionAlongLine: \forall (interval: Directional.ParameterInterval) ->
  \forall (p, v: M.Point) -> \forall (i: M.Coordinate) ->
  Directional.HasDirectionalDerivativeAlong (Space.projection i)
    (Directional.line interval p v) (v i) :=
  \fun (interval: _) (p: _) (v: _) (i: _) =>
    DirectionalLaws.projectionDirectionalDerivative (Directional.line interval p v) v
      (DirectionalLaws.lineTangent interval p v) i;
```

```sh
cargo run --quiet --bin cli -- libs/calculus
cargo run --quiet --bin cli -- tests/projects/library
```
