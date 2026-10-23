# 線形代数

`Commutative[K := K, scalarRing := ring]` は任意の可換環上の `std.Alg.Ring.RingModule` を扱う。
以下の `Space` はその具体化を指す。
有限自由加群・多重線形形式・外代数・標準基底上の行列式は零環にも適用できる。
`Field.Space` は体の逆元を使うスカラーの消去則を提供する。
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

## 滑らかな局所枠のための有限次元構成

`Euclidean` は有限和による標準内積、正定値性、正規化、随伴と直交射影を持つ。
`Euclidean.Matrix.OfIsometry` は正規直交列の像と直交補空間への射影を作る。
`Euclidean.Gram.Factorization` と `Step` は単射な列行列を正規直交枠と三角同型に分解し、`Gram.Of` は像上の逆写像と直交分解を与える。
`Euclidean.OnProjection.Resolution` はトレースで指定した階数の直交射影の枠を帰納的に作る。
`Euclidean.Blocks` と `Space.CoordinateSum` は連続する座標ブロックと直和を同一視する。
`Space.CoordinateBasis` は座標同型から実際の有限基底とその次元を復元する。
`Space.Pullback` は明示的な全単射を通してベクトル空間を移し、`Isomorphism.OfBijective` は全単射な線形写像の逆を構成する。

## 共通の Hermitian 幾何

`Hermitian.Real` と `Hermitian.Complex` は実数・複素数の体、共役、実数の埋め込みと実部を具体化する。
`Hermitian.Over.Inner` は Hermitian 形式と正定値性を分け、`Of.Normalize` は平方根による正規化を構成する。
`Of.Algorithm.exists` は正定値形式と単射な列行列の Gram–Schmidt 分解を有限列の長さについて帰納的に構成する。
`Of.Matrix` は随伴座標を、`Of.Gram.Of` は枠の左逆・像上の逆座標・直交射影を与える。
`Hermitian.Complex.FromInnerProduct` は既存の `Complex.InnerProduct` をこの共通形式へ移す。
既存の実正規化と Gram–Schmidt の分解証明もこの共通実装を利用する。
連続性、局所枠、Hermitian 行列、ユニタリ群と直和は [hermitian_frames](../hermitian_frames/README.md) を参照。

有限基底を持つ線形写像の特性多項式と Cayley–Hamilton、互いに素な因子に対応する不変部分空間への射影は [polynomial_linear_algebra](../polynomial_linear_algebra/README.md) を参照。
