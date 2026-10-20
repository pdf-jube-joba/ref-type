# 点集合位相

位相・部分空間、連続写像、コンパクト性、分離性を扱う。

| module | 公開する内容 |
| --- | --- |
| `Structures` | 台集合を parameter に持つ共通の位相データ・法則・位相の型。 |
| `Topology` | 位相、生成位相、開被覆、コンパクト性と分離性。 |
| `Topology.Ext` / `IndexedIntersections` | 開集合族による位相の外延性、有限個の座標条件の開性・閉性。 |
| `Topology.Subspace` | 部分空間位相、部分空間の開集合の ambient な開集合による表示。 |
| `Topology.Subspace.Properties` / `metric_spaces.MetricSpace.Topology.Hausdorff` | 部分空間のコンパクト性・Hausdorff 性、距離位相の Hausdorff 性。 |
| `Topology.Finite` / `Topology.Closure` | 有限交叉・閉集合の有限和、閉包とその最小性。 |
| `Topology.Interior` | 内部の開性、包含関係、内部に含まれる開集合の最大性。 |
| `Topology.Compactness` | 空集合・一点集合・二集合の和のコンパクト性、閉部分集合、Hausdorff 空間のコンパクト集合の閉性、コンパクト Hausdorff 空間の正規性。 |
| `Compactness` | コンパクト集合の連続像と、連続な全射の値域のコンパクト性。 |
| `Continuity.closedPreimage` | 連続写像による閉集合の逆像の閉性。 |
| `Continuity.Covers.pullback` | 全空間の開被覆を連続写像で引き戻した開被覆。 |
| `Topology.OpenCovers` | 開被覆の族と被覆条件を保持する台集合。 |
| `Homeomorphism` | 同相写像、逆写像、合成。 |
| `LocallyCompact` | コンパクト近傍、局所コンパクト性、コンパクト空間の局所コンパクト性。 |


`Maps.Separate` は Hausdorff 空間への連続写像で像が異なる点を分離する。
`Continuity.Covered` は開被覆上の制限の連続性から全体の連続性を導く。
`Retract.On.With` は連続な包含と左逆写像から、像の部分空間との明示的な同相を作る。
