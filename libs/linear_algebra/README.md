# 線形代数

`Field.Space[K := K, field := field]` は任意の体 \(K\) 上の線形代数を提供する。
ベクトル空間には既存の `std.Alg.Ring.RingModule` を使い、体から得られる環をスカラー環とする。
`Real.field` は Dedekind 実数、`Complex.field` は実数対で構成した複素数の体である。

| モジュール | 内容 |
| --- | --- |
| `Field.Space` | 体の演算と法則、`VectorSpace`、スカラー自身のベクトル空間 |
| `Space.Coordinates` | 添字集合から体への関数で表す座標空間 |
| `Space.Laws` | 加法の消去、零のスカラー倍、スカラー倍の交換 |
| `Space.Linear` | 線形写像、合成 |
| `Space.Linear.Operations` | 零写像、線形写像の和・スカラー倍・負号 |
| `Space.Subspace` | 部分空間と線形写像の核 |
| `Space.Form` | 双線形形式、対称性、交代性、非退化性、随伴 |
| `Space.Sums` | 有限和、添字列の重複のないこと |
| `Space.Sums.Prop` | 有限和の加法・スカラー倍、二重和の交換 |
| `Space.Finite` | 有限基底、座標と復元、次元、有限次元性、トレース |
| `Space.Finite.Prop` | 座標写像の単射性、復元写像の線形性、線形汎関数の基底展開 |
| `Space.Finite.Representation` | 線形写像と行列の双方向の変換、往復の法則、合成と行列積の対応 |
| `Space.Finite.Rebase` | 基底変換行列、異なる添字集合の基底間でのトレースの一致 |
| `Space.Finite.Trace` | 表現行列の対角和との一致、零写像・加法・スカラー倍の法則 |
| `Space.Matrix` | 長方形行列、和、スカラー倍、転置、作用、行列積 |
| `Space.Square` | 対角和、転置・加法・スカラー倍の法則、積の巡回性、行列の固有値・固有ベクトル |
| `Space.Eigen` | 抽象線形写像の固有値・固有ベクトル・固有空間、恒等写像とスカラー写像 |
| `Space.EigenCoordinates` | 固有方程式・非零性・固有ベクトル・固有値の座標表示との同値性 |
| `Real.InnerProduct` | 実内積、直交、自己随伴、等長写像、双線形形式への接続 |
| `Complex.InnerProduct` | エルミート内積、直交、自己随伴、等長写像、自己随伴写像の固有値の実数性 |
| `Complex.Matrix` | 成分の共役、共役転置 |
| `Complex.Square` | エルミート行列 |

表の `Space` は `Field.Space` の具体化を指す。
各ベクトル空間は `zero`、`add`、`neg`、`smul` とそれらの法則を持つ。
線形写像は `apply` と零・加法・スカラー倍の保存をまとめた構造である。

## 有限基底と行列表示

有限基底は、重複のない有限添字列、基底ベクトル、線形な座標写像を持つ。
`reconstruction` と `coordinateReconstruction` は座標写像と有限線形結合による復元が互いに逆であることを表す。
`dualReconstruction` は双対側の復元を表す。
基底 \((b_i)_{i\in I}\) とその座標汎関数 \((\beta_i)_{i\in I}\) の関係は次の式である。

\[
x=\sum_{i\in I}\beta_i(x)b_i,\qquad
\beta\!\left(\sum_{i\in I}a_i b_i\right)=a,\qquad
\sum_{j\in I}a_j\beta_j(b_i)=a_i.
\]

`dimension` は添字列の長さであり、`FiniteDimensional` は基底の存在を表す。
添字集合には `std.Data.FinSet.Fin n` や有限帰納型を使える。
`Matrix` モジュールの成分は行、列の順に指定する。
`Representation.toMatrix b c f` の行は終域の基底 `c`、列は始域の基底 `b` に対応する。

\[
[f]_{c\leftarrow b}(j,i)=\gamma_j(f(b_i)),\qquad
\gamma(f(x))=[f]_{c\leftarrow b}\,\beta(x).
\]

`mapRoundTrip` は行列への変換と復元で写像の作用が保存されることを示す。
`matrixRoundTrip` は任意の行列が線形写像を経由して元に戻ることを示す。
`compositionMatrix` は写像の合成が表現行列の積になることを示す。

## トレースと固有値

有限次元の自己準同型 \(f\) のトレースを基底から計算する。

\[
\operatorname{tr}(f)=\sum_{i\in I}\beta_i(f(b_i)).
\]

`traceIndependent` は添字集合も基底も異なる二つの表示で値が一致することを証明する。
`traceMatrix` はこの値が表現行列の対角和に一致することを示す。
長方形行列についても `Square.Cyclic.traceCyclic` が \(\operatorname{tr}(AB)=\operatorname{tr}(BA)\) を証明する。

固有ベクトルは非零性と固有方程式をまとめた命題であり、固有値はその存在で定義する。

\[
f(x)=\lambda x,\qquad x\ne 0.
\]

`Eigenspace` は固有方程式を満たすベクトルの集合であり、`eigenspace` はその部分空間構造を与える。
`eigenvalueCorrespondence` は抽象写像とその表現行列の固有値が一致することを示す。

## 実数と複素数

双線形形式とその随伴は任意の体上で定義する。
正定値の実内積とエルミート内積は、それぞれ実数と複素数に特殊化する。
複素内積は第1引数について共役線形、第2引数について線形とする。

\[
\langle ax,y\rangle=\overline a\langle x,y\rangle,\qquad
\langle x,ay\rangle=a\langle x,y\rangle.
\]

`selfAdjointEigenvalueReal` は、自己随伴写像の固有ベクトルが与えられたとき、その固有値 \(\lambda\) が `ofReal (re lambda)` に一致することを証明する。
この定理は有限次元性を必要としない。

```text
\import linear_algebra.Real[] \as R;
\import linear_algebra.Field[].Space[K := R.Scalar, field := R.field] \as Algebra;
\import Algebra.Linear[V := V, W := W, source := source, target := target] \as Linear;
\import Algebra.Eigen[V := V, space := source] \as Eigen;
```

[利用例](../../tests/projects/library/src/LinearAlgebraExamples.ref)では、任意の体上の1次元空間、実数と複素数への具体化、0次元空間、複素数のエルミート内積、2次行列の積と固有ベクトルを検査する。

```sh
cargo run --quiet --bin cli -- libs/linear_algebra
cargo run --quiet --bin cli -- tests/projects/library
```
