# 多様体

`Dimension[n := n]` は共通の座標空間 \(\mathrm{Fin}(n)\to\mathbb R\) を使う。
`Chart` は位相空間の開集合と座標空間の開集合の同相をまとめる。
`Chart.Transition` は二つのチャートの実際の重なりを追跡し、遷移写像の定義域の開性を証明する。
`Topological` は Hausdorff 性・第二可算性とチャートによる被覆をまとめ、`Atlas` は順序付きのすべてのチャート対について滑らかさを記録する。
`AtlasData` はアトラスのデータ・法則・互換性・最大性の型を公開する。
`Atlas.saturate` は互換な全チャートから最大アトラスを構成し、`saturateIdempotent` は飽和の冪等性を証明する。
`Smooth.Manifold` は最大アトラスを持ち、`Smooth.From.manifold` は小さいアトラスから構成する。
`SmoothMap[n := n, m := m].Between[M := M, N := N]` は連続写像の座標表示を実際の開集合上に作り、その滑らかさによって多様体間の滑らかな写像を定義する。

`Tangent.On[M].Vector(x)` は点を含むチャートと座標ベクトルの対を、遷移写像のヤコビアンによる同値関係で割った接空間である。
`space(x)` は代表によらない和・スカラー倍から得る実ベクトル空間、`Cotangent(x)` はその双対である。
`At[x].ChartIsomorphism[chart]` と `CotangentCoordinate[chart]` は座標空間との同型を公開する。
`Differential.Between[M, N].At[f, x]` はチャートの選択によらない微分を線形写像として返す。
`DifferentialIdentity`、`DifferentialComposition`、`DiffeomorphismDifferential` は恒等写像・合成・微分同相との整合性を表す。
`OpenSubmanifold.On[M].In[U]` は開部分多様体と包含写像、その微分の同型を構成する。
`SmallAtlasSmoothMap` は選んだアトラスと最大アトラスによる滑らかさの判定を結ぶ。
`Presentation` は同じ最大アトラスを生成する表示の間の恒等微分同相を返す。

`Dimension.Examples.Euclidean` は任意次元の座標空間とその標準アトラスを構成する。
`Euclidean.Subspace` は任意の開部分集合へ制限し、`Examples.Point` は零次元の一点多様体を、`Dimension.Examples.Empty` は任意次元の空多様体を構成する。
利用例は [Geometry.ref](../../tests/projects/manifolds-de-rham/src/Geometry.ref) にある。

```sh
target/debug/cli libs/manifolds --no-cache --diagnostics compact
```
