# 線形代数

`Field.Space[K := K, field := field]` は任意の体 \(K\) 上の線形代数を提供する。
ベクトル空間には既存の `std.Alg.Ring.RingModule` を使い、体から得られる環をスカラー環とする。
`Real.field` は `real.Analysis.Algebra.field` が提供する Dedekind 実数の体、`Complex.field` は実数対で構成した複素数の体である。

| モジュール | 内容 |
| --- | --- |
| `Field.Space` | 体の演算と法則、`VectorSpace`、スカラー自身のベクトル空間 |
| `Space.Isomorphism` | 双方向の線形写像と逆の法則、単射性と全射性。 |
| `Space.DirectSum` | 二空間の積上のベクトル空間構造と、写像を組にする普遍性。 |
| `Space.Coordinates` | 添字集合から体への関数で表す座標空間 |
| `Space.Laws` | 加法の消去、零のスカラー倍、スカラー倍の交換 |
| `Space.Linear` | 線形写像、合成 |
| `Space.Linear.Operations` | 零写像、線形写像の和・スカラー倍・負号 |
| `Space.Subspace` | 部分空間と線形写像の核 |
| `Space.Subspace.Image` / `Space.Quotient` | 線形写像の像、商ベクトル空間と線形写像の降下 |
| `Space.Multilinear` / `Alternating` | 任意次数の多重線形形式・交代形式、零次のスカラー同型、前合成、収縮と符号変換 |
| `Space.Multilinear.Finite` / `Alternating.Finite` | 全引数の基底展開、復元公式、基底上の等式判定 |
| `Space.FiniteCoordinates` | 任意次元の座標空間の標準有限基底 |
| `Alternating.PermutationRule` | 任意の有限全単射の交換列への分解と交代形式の符号変換則 |
| `Alternating.Dimension.Above` | 次元より高い次数の交代形式の零性 |
| `Space.Shuffle` / `Sign` | 符号付き分割の有限和、次数、双線形性・結合則・単位・符号付き交換則 |
| `Space.Exterior.Degrees` | 任意次数の交代形式の外積、タプルとリストによる相互変換 |
| `Exterior.Bilinearity` / `Associativity` / `UnitLaws` / `GradedCommutativity` | 外積の代数法則 |
| `Exterior.Pullback.Naturality` | 線形写像による前合成が外積を保つこと |
| `Space.Subspace.Of` | 部分空間上のベクトル空間と線形な包含 |
| `Space.Dual` / `Space.Dual.Precomposition` | 線形汎関数の空間、評価、線形写像による反変な引き戻し |
| `Space.Tensor` / `Space.Tensor.Universal` | 双線形評価で定める商、純テンソル、双線形写像を一意に降ろす普遍性 |
| `Space.Form` | 双線形形式、対称性、交代性、非退化性、随伴 |
| `Space.Sums` | 有限和、添字列の重複のないこと |
| `Space.Sums.Prop` | 有限和の加法・スカラー倍、二重和の交換 |
| `Space.Finite` | 有限基底、座標と復元、次元、有限次元性、トレース |
| `Space.Finite.Prop` | 座標写像の単射性、復元写像の線形性、線形汎関数の基底展開 |
| `Space.Finite.Representation` | 線形写像と行列の双方向の変換、往復の法則、合成と行列積の対応 |
| `Space.Finite.Rebase` | 基底変換行列、異なる添字集合の基底間でのトレースの一致 |
| `Space.Finite.Trace` | 表現行列の対角和との一致、零写像・加法・スカラー倍の法則 |
| `Space.Finite.Dimension` / `Space.Finite.Dual` | 基底の長さのスカラー値の一致、双対基底の構成と次元の法則 |
| `Real.Dimension.Space` / `Complex.Dimension.Space` | 自然数の埋め込みの単射性による実数・複素数上の次元の不変性 |
| `Space.Matrix` | 長方形行列、和、スカラー倍、転置、作用、行列積 |
| `Space.Square` | 対角和、転置・加法・スカラー倍の法則、積の巡回性、行列の固有値・固有ベクトル |
| `Space.Eigen` | 抽象線形写像の固有値・固有ベクトル・固有空間、恒等写像とスカラー写像 |
| `Space.EigenCoordinates` | 固有方程式・非零性・固有ベクトル・固有値の座標表示との同値性 |
| `Real.InnerProduct` | 実内積、直交、自己随伴、等長写像、双線形形式への接続 |
| `Complex.InnerProduct` | エルミート内積、直交、自己随伴、等長写像、自己随伴写像の固有値の実数性 |
| `Complex.Matrix` | 成分の共役、共役転置 |
| `Complex.Square` | エルミート行列 |

表の `Space` は `Field.Space` の具体化を指す。
有限基底は、重複のない添字列、基底ベクトル、線形な座標写像と往復の法則を保持する。
`FiniteCoordinates.Exterior.word` は座標共変ベクトルの外積を任意次数で構成する。
`IncreasingBasis` は増加添字列の有限性と重複のない列挙を公開し、その列挙について係数から形式を復元する。
`FiniteExterior.At.reconstruction` は選んだ有限基底の座標写像を用いて、一般の有限次元ベクトル空間にも同じ復元を与える。
外積は引数列を左右へ分配した有限和として構成し、右へ分配する引数が左の引数を横切る数から符号を定める。
各次数の形式を、その次数以外の引数列で零となるリスト上の関数へ埋め込む。
`componentWedge` はこの埋め込みと shuffle の積との一致を、`Components.ext` は埋め込みによる等式判定を示す。
次数の加算順序が異なる結合則と交換則は、この共通の関数空間で比較する。
`Representation.toMatrix b c f` の行は終域の基底 `c`、列は始域の基底 `b` に対応する。
`Rebase.traceIndependent` は添字集合も基底も異なる二つの表示でトレースが一致することを示す。

複素内積は第1引数が共役線形、第2引数が線形である。
`selfAdjointEigenvalueReal` は自己随伴写像の固有値の実数性を示し、有限次元性を要求しない。

[利用例](../../tests/projects/library/src/LinearAlgebraExamples.ref) は有限基底・行列・固有値と実数・複素数への具体化を検査する。

検査方法は [ライブラリ一覧](../README.md#型検査) を参照。
