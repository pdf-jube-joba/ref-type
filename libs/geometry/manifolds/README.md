# 多様体

`Dimension[n := n]` は座標空間 \(\mathrm{Fin}(n)\to\mathbb R\) を使う。

| module | 内容 |
| --- | --- |
| `Chart.Transition` | 開集合の同相と遷移写像 |
| `Topological` / `AtlasData` / `Atlas` | Hausdorff・第二可算な被覆と滑らかなチャート変換 |
| `Atlas.saturate` / `Smooth.From` | 最大アトラス、小さいアトラスからの構成 |
| `SmoothMap.Between` | 実際の開集合上の座標表示による滑らかな写像 |
| `Tangent.On.At` | チャート・ベクトル対の商、接空間と余接空間、座標同型 |
| `Differential.Between.At` | チャートによらない微分 |
| `DifferentialIdentity` / `DifferentialComposition` / `DiffeomorphismDifferential` | 恒等・合成・微分同相の法則 |
| `OpenSubmanifold.On.In` | 開部分多様体、包含とその微分 |
| `SmallAtlasSmoothMap` / `Presentation` | アトラスによる滑らかさ判定、表示間の恒等微分同相 |
| `SmoothCover` / `Tangent.On.Transport` | ユークリッド開集合の開被覆上での滑らかな写像の貼り合わせ、等しい底点間の接ベクトルと座標の移送 |
| `Dimension.Examples` | Euclid 空間、開部分集合、一点・空多様体 |
| `EuclideanMap.Between` / `ChartMap.On.At` | 開集合間の写像の多様体上の写像への変換、チャートによる滑らかなパラメータ表示 |

[Geometry.ref](../coordinate_calculus/src/Geometry.ref) に利用例がある。
