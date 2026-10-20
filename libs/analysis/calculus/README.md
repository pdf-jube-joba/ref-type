# 微分

Dedekind 実数上の極限と微分を扱う。

| module | 内容 |
| --- | --- |
| `Real` | 実数の演算、定数・恒等・一次関数 |
| `Real.Limit.Def` / `Prop` | 点を除いた ε–δ 極限、定数・恒等関数、一致による移送 |
| `Real.Derivative.Def` / `Prop` / `Operations` / `Product` / `Chain` | 差商の極限、微分の一意性、連続性、和・積・連鎖律 |
| `Real.MeanValue.Interval` | Fermat・Rolle・平均値定理、導関数による差分評価 |
| `Real.Multivariable[n].Space.Def` | 有限座標と最大値ノルム（零次元では零） |
| `Real.Multivariable[n].Partial.Def` / `Differential.Def` / `Directional.Def` | 偏微分・勾配、全微分、曲線に沿う方向微分 |
| `Real.Multivariable[n].Smooth.Def` | 反復偏導関数、\(C^k\) 級と \(C^\infty\) 級 |
| `Real.Multivariable[n].Open` / `Open.Smooth` | 開集合への制限、相対的偏微分、演算と貼り合わせ |
| `Open.C1` / `Open.Smooth.Differential` / `Open.Smooth.Mixed` / `Real.Schwarz.Rectangle` | 連続偏導関数による全微分、二重平均値定理、混合偏微分の交換 |
| `Maps[n, m]` / `Maps.Composition` / `Vector[n, m]` | 開集合間の滑らかな写像、ヤコビアン、ベクトル値全微分と連鎖律 |
| `Maps.WithPartials` / `Maps.Preimage` | 連続な偏微分を持つ写像の連鎖律、開集合の逆像への制限 |
| `Real.OneDimension` / `Blocks[n, m]` | 実変数の微分と一次元偏微分の対応、座標ブロックの積と射影・切片 |
| `Curves[n]` / `Maps.Corestriction` | 滑らかな実変数曲線の全域代表と微分、値域を開集合に制限した写像の微分 |
| `Scaling[n]` / `Translation[n]` | 滑らかな拡大写像と平行移動、平行移動の微分 |
| `Identity[n]` / `Diffeomorphism[n, m]` | 恒等写像、微分同相の逆・合成と誘導同相 |

`ContDiff k f` は k 階までの微分の仕様と連続性を持つ族の存在、`Smooth f` はすべての k に対する `ContDiff k f` である。
`Open.Smooth.Derivative.Function U` が滑らかな関数を受け取り、`derivative U f i` が滑らかな偏導関数を返す。
`Maps.Differential[U, V, f, a].value` は `linear_algebra` の線形写像、`matrixEntry` は滑らかなスカラー関数である。

`Directional` は零を含む開区間上の曲線を使い、二側極限を取る。
`HasDirectionalDerivativeAt` は同じ始点と接ベクトルを持つすべての曲線について量化し、接ベクトルはパラメータに対する速さを含む。

利用例は[Calculus.ref](../../geometry/coordinate_calculus/src/Calculus.ref)と[非線形な微分同相](../../geometry/coordinate_calculus/src/Shear.ref)を参照。

`Real.Derivative.SquareRoot` は正の値をとる微分可能な関数の平方根を微分する。
`Real.Multivariable.Open.Analysis.SquareRoot` はこれを偏微分へ移し、`Open.Smooth.SquareRoot` は正の滑らかな関数の平方根が滑らかであることを証明する。
高階の滑らかさは、平方根を \(r=\sqrt f\) として \(\partial_i r=\frac12 r f^{-1}\partial_i f\) を用いて帰納的に示す。

## 行列族と局所正規直交枠

`LinearFamily` と `MatrixFamily` は滑らかな係数行列の作用 \((u,v)\mapsto A(u)v\) を有限和から構成する。
`Maps.Tangent` は \((u,v)\mapsto(f(u),Df_u v)\)、`Maps.FixedDifferential` は固定ベクトルへの微分の作用を滑らかな写像として公開する。
`SmoothCoordinates` は有限内積と座標の結合を扱う。
`GramSchmidt.On.Rank` は滑らかな単射行列族を滑らかな正規直交枠と可逆な係数行列に分解する。
その `Projections` は接方向・法方向の滑らかな直交射影と像上の逆写像を与える。
`ProjectionFrames` は一定階数の滑らかな直交射影から、正値ノルムの開近傍上で正規直交枠を構成する。
`InverseFamily` は滑らかな可逆行列族の点ごとの逆の滑らかさを導き、`LinearMap` は線形写像の滑らかさと微分の公式を共有する。
