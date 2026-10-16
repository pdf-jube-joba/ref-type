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
| `CW` / `Attach` / `Pair` | 有限 CW 複体、セル付着、部分複体と商 |

`FiniteComplex` は特性写像・境界の付着・Hausdorff 条件・弱位相を保持する部分集合型である。
円板の開集合は有限座標の距離による `Euclidean.OpenInDisk` で記述する。
`Cofibration.ForTarget.homotopyExtension` は cofibration 条件を前提に延長を証明する。

`Cone` と unreduced suspension は cylinder の商なので、入力空間が空なら空になる。
`Cone.Contraction.contract` は入力空間の点を受け取る。
reduced suspension と smash は入力の基点を受け取る。

[利用例](../cell_spaces/src/root.ref)には区間、円板・球面、一次元セルの付着、空の CW 対、次数付き単体がある。
検査方法は[ライブラリ一覧](../../README.md#型検査)を参照。
