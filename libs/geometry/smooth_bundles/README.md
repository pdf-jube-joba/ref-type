# 滑らかなベクトル束

`Real[n,r].On[M].Family[F,space]` と `Complex[n,r].On[M].Family[F,space]` は、第二可算 Hausdorff な実多様体上の、階数一定の実・複素滑らかなベクトル束を構成する。
`Bundle[I]` は基底多様体のチャートとファイバーの線形同型からなる被覆、および重なり上の滑らかな遷移行列を持つ。
`Of[I,bundle].manifold` は局所座標から実際に構成した全空間の滑らかな多様体である。
実束の全空間の次元は \(n+r\)、複素束では \(n+2r\) となる。

## 切断・写像・忘却

`Of.Sections` の切断はファイバーの元の族であり、その全空間への写像が滑らかであることを要求する。
零切断、基底への射影とその式を公開する。
複素束の切断は実化した滑らかな束の切断と同じ型である。
`Maps[n,r,s]` と `ComplexMaps[n,r,s]` は同じ基底上の実線形・複素線形な滑らかな束写像である。
`Applying` は切断への作用、`After.Of` は束写像の合成を、全空間の滑らかな写像の合成から構成する。
`Of.Identity.map` は恒等束写像である。

実束の `Of.Forget.forget`、複素束の `Of.Forget.continuous` は [vector_bundles](../vector_bundles/README.md) の束を構成する。
全空間の位相、各局所自明化とその逆の連続性を証明し、滑らかな全空間との `homeomorphism`、または両方向の `embed`・`recover` を公開する。
複素束の `Of.forget` は、これとは別に、階数 \(2r\) の実滑らかな束を返す。

## 線形演算と計量

| `Of` 以下の API | 構成 |
| --- | --- |
| `Dual.dual` | 線形汎関数の束。逆遷移行列から滑らかさを証明する。 |
| `Paired.Using.directSum` / `Paired.Using.DirectSum.directSum` | 同じ基底チャート被覆に揃えた二つの束の直和。 |
| `Paired.Using.Tensor.tensor` | 代数的テンソル積の束。有限和の係数式から滑らかさを証明する。 |
| `Alternating.alternating` | ファイバー上の交代形式の束。 |
| `Exterior.exterior` | 双対空間上の交代形式としての共変外冪束。 |
| `Columns.columnsBundle` | ファイバーの有限個の列からなる束。 |
| `Metrics.existsMetric` | 任意の束に対する滑らかな正定値計量の存在。 |

`Paired` はもう一方の束の局所枠を同じ基底チャート上で受け取り、`Using` にその遷移関数の滑らかさを渡す。
テンソル積と外冪の座標には [bundle_operations](../bundle_operations/README.md) の有限添字の列挙を渡す。
`PairIndices.existsEnumeration`、`ExteriorIndices.existsEnumeration` が列挙の存在を与える。
零階数と零次外冪も同じ構成に含まれる。

計量の存在証明は [smooth_partitions](../smooth_partitions/README.md) の従属分割を使用する。
局所枠での標準計量を重み付き線形写像で引き戻し、局所有限和を取る。
重みを \(\rho_i\) とすると、局所項は \(\rho_i^2 h_i\) である。
\(\sum_i\rho_i=1\) と各項の非負性から正定値性を導き、閉じた台の外での零延長と局所有限性から全係数の滑らかさを証明する。
被覆の添字型が空の場合も扱う。
Hermitian 形式は第一変数に共役線形、第二変数に線形とする。

## 一般線形群・枠束・随伴束

`GeneralLinear` は有限次元線形自己同型の群を構成する。
`MatrixModel.homeomorphism` は係数行列の行列式が非零となる開部分空間との同相であり、行列積と逆行列の連続性も証明する。
`RealLinear.Smooth` と `ComplexLinear.Smooth` は滑らかな行列族の積と逆を証明する。
複素の場合は実部・虚部の座標によって実微分可能性を扱う。

`Of.Frames` のファイバーは線形同型 \(\phi:F_x\to K^r\) である。
右作用を \(\phi\cdot g=g^{-1}\phi\) とし、作用の恒等・合成則、自由性・推移性を証明する。
`Frames.Local` は局所枠と \(GL_r(K)\) の間の互いに逆な座標を持つ。
局所座標は \(c_i\phi^{-1}\)、チャート変更は \(g\mapsto(c_jc_i^{-1})g\) であり、`coordinateFormula` と `coordinateSmooth` がその式と滑らかさを与える。
`actionFormula` と `actionSmooth` は右作用の局所行列表示を与える。

`Of.Frames.Smooth[enumeration].manifold` は、列の束のうち基底をなす列からなる開部分多様体である。
`Columns.FrameBundle` で可逆性と行列式非零の同値、開性、枠との対応、列からの一意な枠の復元、右作用と滑らかな射影を証明する。
`Frames.Smooth.groupManifold` は非特異行列の実座標による GL の滑らかな多様体であり、`toGroupPoint`・`fromGroupPoint` が線形同型との対応を与える。
`Frames.Smooth.Local[i].diffeomorphism` は、枠束の第 \(i\) 基底チャート上の開部分と、基底座標像と GL の開部分の積との実際の `Diffeomorphism` である。
その順写像・逆写像はいずれも `manifolds.SmoothMap` の値で、`basePreserved` が基底への射影の一致、`groupFormula` が GL 成分と局所枠座標の一致を証明する。
`ChartDomain.On.At` は、この構成に使うチャート定義域と座標像の微分同相を構成する。

`Frames.Smooth.Action.productManifold` は、枠束と実行列座標の自明束を非特異行列の開部分へ制限して得る積多様体である。
`firstMap` と `secondMap` はその滑らかな両射影であり、`Pair[d].From[X].Of[f,g].map` は任意の滑らかな写像の組からの滑らかな組写像を返す。
`Frames.Smooth.Action.map` は、この積多様体から枠束への実際の滑らかな右作用写像である。
`formula` が元の線形同型による右作用との一致を、`identity` と `composition` がこの滑らかな写像の作用則を証明する。
各局所作用の座標表示を行列積の滑らかな写像として構成し、チャート被覆上の一致式から全体の `SmoothMap` を貼り合わせる。

`RealLinear.Representation` と `ComplexLinear.Representation` は滑らかな群表現である。
滑らかさは任意の有限次元の滑らかな行列パラメータ族を保存することとして記述する。
恒等表現 `standard` も構成する。
`Of.Associated[s,representation].associated` は元の遷移関数 \(\tau_{ij}\) に表現を作用させた \(\rho(\tau_{ij})\) から束を貼り合わせる。
恒等・三重重なりの cocycle 則、貼り合わせたファイバーの局所線形同型、実際の遷移行列の式と滑らかさを証明する。

## 既存の幾何学との比較

`Tangent.On.bundle` と `Normal.On.Of.bundle` は既存の接束・法束の局所枠を一般の滑らかな束に移す。
接束は `FrameComparison.diffeomorphism`、法束は全空間の位相と射影の一致を公開する。
`Normal.On.Of.Splitting.directSum` は一般の直和束であり、既存の接束と法束の分解と同じ全空間の位相を持つ。
`Splitting.diffeomorphism` は周囲の自明束との既存の分解写像を公開する。
`Stabilization.diffeomorphism` は安定化した法束と元の法束のスカラー積との微分同相、`splittingCompatibility` は直和分解との整合式を公開する。

[Examples](src/Examples.ref) は零次元の基底上の零階数の実・複素束に計量を与え、両スカラーの恒等表現を使用する。
