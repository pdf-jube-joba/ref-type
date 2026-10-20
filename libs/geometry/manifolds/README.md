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

## 束の全空間とはめ込みの基盤

`IndexedAtlas` は任意の集合で添字付けた局所パラメータから位相と滑らかな構造を作る。
`BundleAtlas.Over` は底空間のチャートと有限座標の局所積を共有し、底空間の第二可算性から可算部分被覆を選び、全局所座標で定義した位相の第二可算性を証明する。
異なる底点は底空間で、同じ底点の異なるファイバー点は一つの局所積で分離する。
`FromCharts.Between.Covered` は最大アトラスを列挙することなく、被覆する小さいアトラスから滑らかな写像を作る。
`ChartRestriction` はチャート像の開集合へ制限し、`GlobalChart` は全点を含む一つのチャートから明示的な微分同相を作る。

`Immersion.Between.IsImmersion` は各点の微分が単射であることを表す。
`IsEmbedding` は、はめ込みであり像の部分空間への同相を与えることを表す。
`EmbeddingLaws` は点の単射性と開集合の周囲への持ち上げを用いる等価な条件で、`embeddingCriterion` が両者を結ぶ。
`OfEmbedding.homeomorphism` は像の部分空間位相への実際の同相を構成する。
`ImmersionIdentity`、`ImmersionComposition`、`DiffeomorphismImmersion` が恒等・合成・微分同相による前後合成を扱う。
`EmbeddingRetraction` は滑らかな左逆写像から埋め込みを構成する。
`EuclideanGlobal`、`EuclideanLinear`、`EuclideanPair` は全ユークリッド空間上の具体的な写像とその微分を多様体 API に渡す。
接束と法束の利用例は [tangent_normal](../examples/tangent_normal/README.md) にある。
