# 微分

Dedekind 実数上の関数の極限と微分を扱う。
実数の演算には `real.DedekindReal.Arithmetic.Prop` の符号付きの乗法・逆数を使い、距離には `real.Analysis.Distance` を使う。

| モジュール | 内容 |
| --- | --- |
| `Real` | 実数の型と演算、定数関数、恒等関数、一次関数 |
| `Real.Limit.Def` | ε–δ 極限 `HasLimitAt` と半径の条件 `Control` |
| `Real.Limit.Prop` | 定数・恒等関数の極限、点を除いた関数の一致による極限の移送 |
| `Real.Derivative.Def` | 差商 `slope`、微分 `HasDerivativeAt`、微分可能性、導関数付きの関数 |
| `Real.Derivative.Prop` | 定数・恒等関数・一次関数の微分則と微分可能な関数の構成 |
| `Real.Derivative.Operations` / `Product` / `Chain` | 一意性、連続性、和・積・合成の微分則 |
| `Real.MeanValue.Interval` | Fermat・Rolle・平均値定理と導関数による差分評価 |
| `Real.Multivariable[n].Space.Def` | \(\mathbb{R}^n\) の座標、座標の置換、最大値ノルムと連続性 |
| `Real.Multivariable[n].Partial.Def` | 偏微分、勾配、二階混合偏微分の交換可能性 |
| `Real.Multivariable[n].Differential.Def` | 線形写像、全微分と全微分可能性 |
| `Real.Multivariable[n].Directional.Def` | 開区間上の曲線に沿う方向微分、接ベクトルと一致の条件 |
| `Real.Multivariable[n].Smooth.Def` | 反復偏導関数、\(C^k\) 級、\(C^\infty\) 級と微分順序の交換可能性 |
| `Real.Multivariable[n].Open` | 開集合、部分集合型の台集合、制限と包含 |
| `Open.Smooth` | 相対的な偏微分による滑らかさ、偏微分、和・積・制限と開被覆による貼り合わせ |
| `Open.C1` / `Open.Smooth.Differential` | 連続偏導関数による全微分と滑らかな関数の全微分の値 |
| `Real.Schwarz.Rectangle` / `Open.Smooth.Mixed` | 二重平均値定理と滑らかな混合偏微分の交換則 |
| `Maps[n, m]` / `Maps.Composition` | 開集合間の滑らかな写像、合成、ヤコビアンとその合成則 |
| `Vector[n, m]` | ベクトル値全微分、一意性、線形写像の微分と連鎖律 |
| `Identity[n]` / `Diffeomorphism[n, m]` | 恒等写像、滑らかな逆写像、微分同相の逆・合成と誘導同相 |

## 定義の要点

`HasLimitAt f a l` は点 `a` を除いた ε–δ 極限、`HasDerivativeAt f a m` は差商の極限である。
`DifferentiableFunction` は関数・導関数・微分則をまとめる。

`Real.Multivariable[n := n]` の `Point` は `Fin n -> Real`、ノルムは最大値ノルムであり、`n=0` では零とする。
`Partial` は偏微分と勾配、`Differential` は線形写像による全微分、`Smooth` は座標の有限列で指定する反復偏導関数を扱う。
`ContDiff k f` は k 階までの微分の仕様と連続性を持つ族の存在、`Smooth f` はすべての k に対する `ContDiff k f` である。
全空間版の微分順序の交換条件に加え、開集合版の `Open.Smooth.Mixed.commute` は滑らかさから混合偏微分の交換を証明する。

開集合版では `Open.Smooth.Derivative.Function U` が滑らかな関数を値として受け取り、`derivative U f i` が滑らかな偏導関数を返す。
導関数の一意性から証人の選択によらないことを証明する。
`Maps.Differential[U, V, f, a].value` は共通の `linear_algebra` の線形写像であり、`matrixEntry` は滑らかなスカラー関数である。
滑らかな合成の証明は各階数について反復偏導関数の族を構成する。
非線形な微分同相と合成の利用例は [Shear.ref](../../tests/projects/manifolds-de-rham/src/Shear.ref) にある。

`Directional` の曲線は零を含む開区間を定義域とする。
`HasDirectionalDerivativeAlong` は曲線に沿う差商の二側極限、`HasDirectionalDerivativeAt` は同じ始点と接ベクトルを持つすべての曲線についての条件である。
接ベクトルにはパラメータに対する速さを含む。

[利用例](../../tests/projects/library/src/root.ref) と [検査方法](../README.md#型検査) を参照。
