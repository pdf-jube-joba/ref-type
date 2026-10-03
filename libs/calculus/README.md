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

`HasLimitAt f a l` は、任意の \(\varepsilon>0\) に対して \(\delta>0\) が存在し、\(x\ne a\) かつ \(d(x,a)<\delta\) ならば \(d(f(x),l)<\varepsilon\) が成り立つことを表す。
`HasDerivativeAt f a m` は、差商
\[
\frac{f(x)-f(a)}{x-a}
\]
の \(x\to a\) における極限が \(m\) であることを表す。

微分則は、定数関数の導関数が零、恒等関数の導関数が一、一次関数 \(x\mapsto mx+b\) の導関数が \(m\) であることを証明する。

```text
\import calculus.Real[] \as C;
\import C.Derivative[].Def[] \as D;
\import C.Derivative[].Prop[] \as Laws;

\definition affineDerivative: \forall (m, b, a: C.Real) ->
  D.HasDerivativeAt (C.affine m b) a m := Laws.affineDerivative;

\definition affineFunction(m, b: C.Real): D.DifferentiableFunction::[Set] :=
  Laws.affineDifferentiable m b;
```

`DifferentiableAt f a` はその点での微分係数の存在、`HasDerivative f g` はすべての点で \(g(a)\) が微分係数であることを表す。
`DifferentiableFunction` は関数と導関数を持つ `\structure` であり、`differentiable` フィールドが微分則を保持する。

```sh
cargo run --quiet --bin cli -- libs/calculus
cargo run --quiet --bin cli -- tests/projects/library
```
