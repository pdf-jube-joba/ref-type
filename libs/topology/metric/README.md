# 距離空間と実数値連続関数

距離位相、距離化、実数直線、実数値関数、有限従属分割を扱う。

| module | 公開する内容 |
| --- | --- |
| `metric_spaces.MetricSpace.Compactness` / `Uniform` | コンパクト距離空間の開被覆の Lebesgue 数、連続写像の一様連続性。 |
| `metric_spaces.MetricSpace.Subspace` | 部分集合への距離の制限と、距離位相と部分空間位相の一致。 |
| `metric_spaces.MetricSpace.Lipschitz.Between` | Lipschitz 評価から導く一様連続性と連続性。 |
| `metric_spaces.MetricSpace.Sequences` / `Complete` | Cauchy 列、極限・有界性の保存、完備距離空間、収縮率 \(1/2\) の不動点定理、逐次閉部分集合の完備性。 |
| `metric_spaces.BoundedFunctions.On` | 中心から一様に有界な関数の上限距離と完備性。 |
| `metric_spaces.BoundedFunctions.On.Continuous` | 一様極限の連続性、有界連続関数の完備距離。 |
| `metric_spaces.RealLine.CompactIntervals` | 実数の距離位相における閉区間のコンパクト性。 |
| `metric_spaces.RealFunctions.Product` / `Lattice` / `SquareRoot` / `Reciprocal` | 一般の実数値関数の積、最大・最小・絶対値、平方根、非零逆数の連続性。 |
| `metric_spaces.RealFunctions` | 実数値関数の局所連続性判定、和・差、\([0,1]\) に値を持つ関数の積、Urysohn 関数の連続性。 |
| `metric_spaces.RealFunctions.FiniteSums` | 有限個の連続な実数値関数の和の連続性。 |
| `metric_spaces.PartitionOfUnity` | コンパクト Hausdorff 空間の開被覆に従属する有限分割。 |

## 有限従属分割

`metric_spaces.PartitionOfUnity.Of[source := ..., family := ...].Construction` の `existsPartition` は、コンパクト Hausdorff 条件と開被覆から `Partition` の存在を証明する。
`Partition.parts` は有限リストで、各 `Entry` は被覆の開集合、連続な \([0,1]\) 値の関数、その台が開集合に含まれる証明を持つ。
`Partition.total` は、各点で重みの和が \(1\) になることを表す。
台は関数が零でない点の集合の閉包として定義する。

正規性から得る bump 関数 \(f_i\) を有限個選び、

\[
\varphi_i=f_i\prod_{j>i}(1-f_j)
\]

で重みを作る。
選んだ bump 関数のいずれかが各点で \(1\) となることから、重みの和が \(1\) になる。
非負性・連続性・台の包含は、重みの構成を通して保持する。
