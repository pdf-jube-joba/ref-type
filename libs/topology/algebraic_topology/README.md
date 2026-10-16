# 代数的位相の空間構成

実数の閉区間からホモトピー、基点付き空間、セル付着、有限 CW 対を構成する。

| module | 内容 |
| --- | --- |
| `Interval` / `Arithmetic` / `IntervalFunctions` | 単位区間、反転・積・収縮用の時刻演算と連続性 |
| `Cylinder` / `Homotopy` | cylinder、端点条件、定数・反転・相対ホモトピー |
| `Homotopy.Composition` / `Concatenation` / `RelativeConcatenation` / `RelativeRelation` | 前後合成、閉半区間の貼り合わせによる連結、相対ホモトピーの同値関係 |
| `HomotopyEquivalence` / `Composition` / `Inverse` | ホモトピー同値、同相からの構成、合成と逆 |
| `Pointed` / `Smash` | 基点付き空間、基点を保つ写像、smash 積 |
| `Collapse` / `Cone` / `Suspension` | 部分集合の崩壊、cone とその収縮、reduced / unreduced suspension |
| `Cofiber` / `Cofibration` / `Cofibration.ForTarget` | mapping cone、cylinder の retraction による cofibration 条件とホモトピー拡張性 |
| `Euclidean.Dimension` / `Geometry` | 有限座標、閉円板・境界球面・内部、ノルムと閉性 |
| `Simplex` / `At` / `Insertion` | 標準単体、次数付きの台集合、面の座標写像 |
| `Simplex.Faces` / `Identities` | 面の連続性と合成恒等式 |
| `Simplex.Vertices` / `Affine` / `AffineIdentity` / `AffineFaces` | 全頂点、アフィン写像の連続性・合成則、面との整合性 |
| `Simplex.Interval` | 一次元単体と単位区間の連続な相互逆、端点と面 |
| `Simplex.Compactness` / `Barycentre` / `Metric` | 閉性・コンパクト性、等重みの重心、最大座標距離と Lebesgue 数 |
| `Simplex.Convex` / `Contraction` | 凸結合の連続性と指定点への収縮 |
| `Simplex.AffineMetric` / `Barycentre` | 頂点間の距離からの直径評価と、重心からの距離の縮小率 |
| `Simplex.Affine.Hull` / `ConvexFamily` | アフィン像の凸閉性と、凸集合の共通部分 |
| `Simplex.BarycentricSubdivision` / `Mesh` | 面の選択列で表す細分セル、アフィン写像の連続性と直径の縮小評価 |
| `Semisimplicial` | 次数付き集合、面の恒等式と、それらを保つ写像 |
| `Simplex.Cylinder` / `CylinderAffine` | cylinder 内のアフィン評価、面・頂点・後合成との公式 |
| `Contraction` / `Interval.Contraction` | 一点とのホモトピー同値、区間の具体的な収縮 |
| `PathComponent` / `IntervalPaths` / `Functions` | 道成分の商、区間上の道との対応、成分上一定な関数の降下 |
| `CW` / `Attach` / `Pair` | 有限 CW 複体、セル付着、部分複体と商 |

`FiniteComplex` は特性写像・境界の付着・Hausdorff 条件・弱位相を保持する部分集合型である。
円板の開集合は有限座標の距離による `Euclidean.OpenInDisk` で記述する。
`Cofibration.ForTarget.homotopyExtension` は cofibration 条件を前提に延長を証明する。

`Cone` と unreduced suspension は cylinder の商なので、入力空間が空なら空になる。
`Cone.Contraction.contract` は入力空間の点を受け取る。
reduced suspension と smash は入力の基点を受け取る。

[利用例](../cell_spaces/src/root.ref)には区間、円板・球面、一次元セルの付着、空の CW 対、次数付き単体がある。
検査方法は[ライブラリ一覧](../../README.md#型検査)を参照。
