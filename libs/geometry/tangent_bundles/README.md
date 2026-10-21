# 接束

境界を持たない有限次元の滑らかな多様体の接束を全空間として構成する。
点ごとの接空間と微分は `manifolds.Tangent.On.At` と `manifolds.Differential` を使う。

`Dimension[n := n].On[M := M]` の `Point` は底点 `base` とその点の接ベクトル `vector` を持つ依存対である。
`Fiber[x].isomorphism` は射影の逆像としてのファイバーと既存の接空間を同一視する線形同型である。
`InChart[c]` の `coordinate` と `point` は相互逆で、座標公式は
\[
(x,v)\longmapsto(\varphi(x),d\varphi_xv)
\]
である。
`Change` は遷移写像 \((u,w)\mapsto(f(u),Df_u w)\) を滑らかな行列族として構成する。
`topology`、`hausdorff`、`secondCountable`、`manifold` が全空間の位相と \(2n\) 次元の滑らかな構造を公開する。
全チャートの局所座標から位相を定義し、第二可算性の証明だけに可算部分被覆を使う。

| API | 内容 |
| --- | --- |
| `SmoothProjection.map` / `SmoothZero.map` | 射影と零切断 |
| `Addition` / `Scaling` | 同じ底点上の加法・スカラー倍、その定義域の多様体と滑らかな写像 |
| `Map.Between.Of[f].map` | 点ごとの微分から得る滑らかな接写像 |
| `Identity.On` / `Composition.Between.Of` | 全空間の関数と滑らかな写像としての関手則 |
| `Diffeomorphism.Between.Of` | 逆写像が逆微分同相の接写像である微分同相 |
| `FrameBundle.Over.Family` | ファイバー線形同型による局所座標の共有構成 |
| `Trivial.On.Covered` | \(M\times\mathbb R^r\) の全空間、積位相との同相、滑らかな対の構成 |
| `ScalarProduct.On.Covered` | 実数そのものを使う \(M\times\mathbb R\) |

`FrameBundle` の構成データと相互逆・線形性の法則は `Local`、`Data` と線形同型にまとめる。
`Using.Build` は滑らかな遷移行列から多様体を作り、`Morphism.Build.Inverse` はファイバー線形同型の滑らかな族から全空間の微分同相を作る。
加法の定義域はファイバー直和、スカラー倍の定義域は実数と束のファイバー積として同じ構成を使う。

公開 API を別 package から使う入口は [tangent_normal](../examples/tangent_normal/README.md) にある。
法束、直和分解と安定化は [normal_bundles](../normal_bundles/README.md) にある。
