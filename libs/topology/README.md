# 点集合位相

位相・部分空間、連続写像、コンパクト性、分離性を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

| module | 公開する内容 |
| --- | --- |
| `Structures` | 台集合を parameter に持つ共通の位相データ・法則・位相の型。 |
| `Topology` | 位相、生成位相、開被覆、コンパクト性と分離性。 |
| `Topology.Subspace` | 部分空間位相、部分空間の開集合の ambient な開集合による表示。 |
| `Topology.Subspace.Properties` / `metric_spaces.MetricSpace.Topology.Hausdorff` | 部分空間のコンパクト性・Hausdorff 性、距離位相の Hausdorff 性。 |
| `Topology.Finite` / `Topology.Closure` | 有限交叉・閉集合の有限和、閉包とその最小性。 |
| `Topology.Compactness` | 空集合・一点集合・二集合の和のコンパクト性、閉部分集合、Hausdorff 空間のコンパクト集合の閉性、コンパクト Hausdorff 空間の正規性。 |
| `Compactness` | コンパクト集合の連続像のコンパクト性。 |
| `Homeomorphism` | 同相写像、逆写像、合成。 |
| `LocallyCompact` | コンパクト近傍、局所コンパクト性、コンパクト空間の局所コンパクト性。 |

検査方法と関連パッケージは [ライブラリ一覧](../README.md) を参照。
