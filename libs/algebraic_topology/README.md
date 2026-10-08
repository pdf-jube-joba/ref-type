# 代数的位相の空間構成

実数の閉区間、積・部分空間・商位相を使い、ホモトピー、基点付き空間、セル付着、有限 CW 対のデータを構成する。
直接依存は `std`、`real`、`topology`、`topological_algebra` である。
公開 module は [root.ref](src/root.ref) にある。

| module | 構成と証明 |
| --- | --- |
| `Interval` / `Interval.Arithmetic` / `IntervalFunctions` | 実数の部分空間 \([0,1]\)、コンパクト性と Hausdorff 性、反転・積・収縮用の時刻演算と連続性。 |
| `Cylinder` | \([0,1]\times X\)、射影、時刻ごとの包含とそれらの連続性。 |
| `Homotopy` | 連続な cylinder 写像と端点条件、定数ホモトピー、反転、相対ホモトピーと部分集合上の端点の一致。 |
| `Homotopy.Composition` | 連続写像による前合成・後合成。 |
| `TimeSubdivision` / `Homotopy.Concatenation` | cylinder の閉半区間による貼り合わせとホモトピーの連結・推移性。 |
| `Homotopy.RelativeConcatenation` / `RelativeRelation` | 部分集合上で固定したホモトピーの連結、反射性・対称性・推移性。 |
| `HomotopyEquivalence` / `Composition` / `Inverse` | 双方向の連続写像とホモトピー逆、同相写像からの構成、ホモトピー同値の合成と逆。 |
| `Pointed` | 位相と基点を持つ空間、基点を保つ連続写像と合成。 |
| `Collapse` | 部分集合を一点へ潰す同値関係、商位相、射影の連続性、商からの写像。 |
| `Cone` / `Cone.Contraction` | cylinder の上端の崩壊、底面と頂点、頂点への連続な収縮ホモトピー。 |
| `Suspension` / `Suspension.Maps` | 上端・下端を別々に潰す商、両極、基点の軌道も潰す reduced suspension、連続写像が誘導する unreduced suspension の写像。 |
| `Smash` | 基点付き積の wedge を潰す商と基点、両座標軸の崩壊。 |
| `Cofiber` | 写像の mapping cone を pushout として構成し、付着の等式を証明する。 |
| `Cofibration` | \(X\cup_A([0,1]\times A)\) への cylinder の retraction による cofibration 条件。 |
| `Cofibration.ForTarget` | retraction から実際の延長を構成し、連続性・初期値・部分空間上の一致を証明する。 |
| `Euclidean.Dimension` / `Geometry` | 有限座標、閉円板・境界球面・内部、ノルムの連続性、円板・球面の閉性、座標の二乗評価と単位区間への評価。 |
| `CW` | 特性写像、内部の同相条件、有限なセル族、Hausdorff 条件、低次元セルへの境界の付着、弱位相を持つ有限 CW 複体。 |
| `CW.Attach` | 境界球面に沿うセル付着を pushout として構成する。 |
| `CW.Pair` | 境界で閉じた部分複体、全体・空の部分複体、部分空間と商空間。 |

`FiniteComplex` は複体の条件を保持する部分集合型であり、セル付着の台集合だけから条件を自動的に得るものではない。
`Cofibration.ForTarget.homotopyExtension` は任意の対象空間・部分集合・値域について量化し、cofibration 条件からホモトピー拡張性を証明する。
CW 対の商と、cofibration の延長定理はそれぞれ独立に利用できる。
`Cone.Contraction.contract` は入力空間の点を受け取り、その点で表示した頂点へ恒等写像を収縮する。
積と商写像の定理を使い、時刻と cone の点の両方についての連続性を証明している。

`CW` の円板の開集合は有限座標の距離による近傍条件 `Euclidean.OpenInDisk` で記述する。
`Cone` と unreduced suspension の台集合は cylinder の商なので、入力空間が空なら空になる。
reduced suspension と smash は入力の基点を受け取る。

[利用例](../../tests/projects/topological-k-theory/src/root.ref) は区間のホモトピーの連結と端点、区間反転のホモトピー同値とその合成、円板・球面の閉性、商の等式、一次元円板の境界を一点へ付着する構成、空の有限 CW 対を検査する。

```sh
target/debug/cli libs/algebraic_topology --no-cache --diagnostics compact
target/debug/cli tests/projects/topological-k-theory --no-cache --diagnostics compact
```
