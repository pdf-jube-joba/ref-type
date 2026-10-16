# 線形代数

`Field.Space[K := K, field := field]` は任意の体上の `std.Alg.Ring.RingModule` を扱う。
以下の `Space` はその具体化を指す。
`Real.field` は Dedekind 実数、`Complex.field` は実数対の複素数を使う。

| module | 内容 |
| --- | --- |
| `Space.Isomorphism` / `DirectSum` / `Coordinates` | 同型、二項直和、座標空間 |
| `Space.Linear.Operations` / `Laws` | 線形写像の演算と加群の法則 |
| `Space.Subspace` / `Subspace.Image` / `Quotient` | 部分空間・核・像・商と写像の降下 |
| `Space.Dual.Precomposition` / `Tensor.Universal` | 双対の引き戻し、テンソル積の普遍性 |
| `Space.Multilinear` / `Alternating` | 多重線形・交代形式、前合成と収縮 |
| `Alternating.Finite` / `PermutationRule` / `Dimension.Above` | 基底展開、符号変換、次元を超える次数の零性 |
| `Space.Shuffle` / `Sign` / `Exterior.Degrees` | shuffle による外積と次数 |
| `Exterior.Bilinearity` / `Associativity` / `GradedCommutativity` / `UnitLaws` / `Pullback.Naturality` | 外積の法則 |
| `Space.Finite` / `Finite.Prop` | 有限基底、座標と復元、次元、トレース |
| `Space.Finite.Representation` / `Rebase` / `Trace` | 行列表現、基底変更、対角和と巡回性 |
| `Space.Finite.Dimension` / `Finite.Dual` | 次元のスカラー値、双対基底 |
| `Space.FiniteCoordinates` / `FiniteExterior.At` | 標準基底、任意次数の外積の基底と復元 |
| `Space.Matrix` / `Square` | 長方形・正方行列、演算、作用、固有値 |
| `Space.Eigen` / `EigenCoordinates` | 抽象線形写像と座標表示の固有値・固有空間 |
| `Space.Form` | 双線形形式、非退化性と随伴 |
| `Real.InnerProduct` / `Complex.InnerProduct` | 実・エルミート内積、直交、等長・自己随伴写像 |
| `Real.Dimension.Space` / `Complex.Dimension.Space` | 次元の不変性 |
| `Complex.Matrix` / `Square` | 共役転置、エルミート行列 |

`Representation.toMatrix b c f` の行は終域の基底 `c`、列は始域の基底 `b`。
`Rebase.traceIndependent` は異なる基底・添字集合での一致を示す。
複素内積は第1引数が共役線形、第2引数が線形で、`selfAdjointEigenvalueReal` は有限次元性を要求しない。
外積の次数移送はリスト上の共通表現で比較する。
[SmallSpaces.ref](src/SmallSpaces.ref) に利用例がある。
