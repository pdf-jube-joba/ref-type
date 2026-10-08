# 点集合位相

位相・連続写像・積・部分空間・距離位相を基礎に、コンパクト性、商位相、貼り合わせ、有限従属分割を扱う。
直接依存は `std` と `real` で、公開 module は [root.ref](src/root.ref) にある。

## 構成と定理

| module | 公開する内容 |
| --- | --- |
| `Structures` | 台集合を parameter に持つ共通の位相データ・法則・位相の型。 |
| `Topology` | 位相、生成位相、開被覆、コンパクト性と分離性。 |
| `Topology.Subspace` | 部分空間位相、部分空間の開集合の ambient な開集合による表示。 |
| `Topology.Subspace.Properties` / `MetricSpace.Topology.Hausdorff` | 部分空間のコンパクト性・Hausdorff 性、距離位相の Hausdorff 性。 |
| `Topology.Finite` / `Topology.Closure` | 有限交叉・閉集合の有限和、閉包とその最小性。 |
| `Topology.Compactness` | 空集合・一点集合・二集合の和のコンパクト性、閉部分集合、Hausdorff 空間のコンパクト集合の閉性、コンパクト Hausdorff 空間の正規性。 |
| `Compactness` | コンパクト集合の連続像のコンパクト性。 |
| `Product.Compactness` | 開集合の局所的な開矩形による表示、tube lemma、コンパクト集合の二因子積。 |
| `RealLine.CompactIntervals` | 実数の距離位相における閉区間のコンパクト性。 |
| `Product.Maps` / `Continuity.Corestriction` | 積の射影と部分空間への値域制限の連続性。 |
| `RelationQuotient` | 同値類の集合に商位相を与え、関係を保つ写像を一意に降ろす構成と連続性。 |
| `Coproduct` / `Pushout` | 位相的直和、写像に沿う貼り合わせ、互換な連続写像の降下。 |
| `Quotient` | 写像の終位相、商写像、商からの写像の連続性の普遍性。 |
| `Homeomorphism` | 同相写像、逆写像、合成。 |
| `Gluing` | 開被覆と有限閉被覆による連続性の貼り合わせ、部分空間への制限からの局所条件の導出。 |
| `Gluing.BinaryClosed` / `Gluing.Pasting` | 二つの閉集合の被覆上での連続性判定と一致する写像の貼り合わせ。 |
| `ProductQuotient` | コンパクト Hausdorff 因子と商写像の積が商写像となる定理。 |
| `RealFunctions.Product` / `Lattice` / `SquareRoot` / `Reciprocal` | 一般の実数値関数の積、最大・最小・絶対値、平方根、非零逆数の連続性。 |
| `RealFunctions` | 実数値関数の局所連続性判定、和・差、\([0,1]\) に値を持つ関数の積、Urysohn 関数の連続性。 |
| `PartitionOfUnity` | コンパクト Hausdorff 空間の開被覆に従属する有限分割。 |
| `FunctionSpace.Of` | 連続写像の集合上の compact-open 位相と、連続写像との前合成の連続性。 |
| `LocallyCompact` | コンパクト近傍、局所コンパクト性、コンパクト空間の局所コンパクト性。 |

有限積のコンパクト性の定理は `Product.Compactness.productCompact` にある。
閉区間の定理 `intervalCompact` は、端点の順序を仮定せず、空区間と一点区間も含む。

## 有限従属分割

`PartitionOfUnity.Of[source := ..., family := ...].Construction` の `existsPartition` は、コンパクト Hausdorff 条件と開被覆から `Partition` の存在を証明する。
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

## 型検査と後続の実装単位

リポジトリのルートで実行する。

```sh
target/debug/cli libs/topology --no-cache --diagnostics compact
```

局所コンパクト空間の一点コンパクト化、compact-open 位相の評価写像の連続性は後続の実装単位となる。
K 理論に接続する分野間の利用例は `_plans/topological-k-theory-libraries.md` の検査計画に沿って追加する。
