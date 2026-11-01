# G03 境界・角付き多様体

## 要件

- 主な実装先は `boundary_manifolds`。
- 半空間と象限のチャートによる境界・角付き多様体、境界面、滑らかな写像を構成する。
- 境界の接束、内向き・外向き方向、neat embedding と積の境界面を定義し、座標変更との整合性を証明する。
- 区間・円板・多様体と区間の積を構成し、既存の境界なし多様体への制限と比較する。

## 依存するタスク

- [G02 逆関数・陰関数と正則値の局所形](g02-inverse-implicit.md)

## 実装

実装済み。
公開 API と仮定は [boundary_manifolds](../../libs/geometry/boundary_manifolds/README.md) にまとめる。

| 要件 | 実装 |
| --- | --- |
| 半空間・象限チャート、多様体と滑らかな写像 | `Model`、`Dimension`、`SmoothMap`、`MapIdentity`、`MapComposition` |
| 境界面と接束 | `Face.On` の残る角を含む面と接束、`Face.Global` の大域的な埋め込まれた面、`Boundary.Of.Build` の半空間被覆からの境界多様体と接束 |
| 内向き・外向き方向と座標不変性 | `OneSided`、`Model.RayControl`、`ConeMap`、`Extensions.Local`、`Tangent.On.At.Cones`、`Differential` |
| neat embedding | `Immersion`、`Neat` の内在的条件と法線座標の判定、`NeatIdentity` |
| 積の境界面 | `Product` の積チャートと因子ごとの面の判定、内在的な境界の和集合則 |
| 区間・円板・多様体と区間の積 | `Sublevel` の G02 局所形からの構成、`Disk`、`Interval`、`Cylinder`、`Examples` |
| 境界なし多様体との比較 | `Boundaryless` の空の座標制約による構成と同相、`Interior` の既存の通常の多様体への制限 |

検査の対象コミット、checker、ソース snapshot と全体検査結果は[検査記録](../../benchmarks/records/boundary-manifolds/README.md)に記録する。
