# 行列式と可逆行列

有限正方行列の行列式、余因子、随伴行列、逆行列とその連続性を扱う。
`Ring[K := K, scalars := ring]` は任意の可換環を対象とし、零環と零次元も含む。
外代数の構成と正規化された最高次形式の証明は、[linear_algebra.Commutative](../linear_algebra/README.md) と共有する。

## 代数的な API

`Ring.At[n := n]` の `Matrix` は `Fin n -> Fin n -> K` で、最初の添字が行、次が列である。
`determinant` は列ベクトルを正規化された最高次形式に代入する。
`cofactor A i j` は第 \(j\) 列を標準基底ベクトル \(e_i\) に置き換えた行列の行列式で、`adjugate A i j = cofactor A j i` と定義する。

| module | 公開する内容 |
| --- | --- |
| `Ring.At` | 行列、積、転置、恒等行列、行列式、列の多重線形性・交代性、行列式の乗法性 |
| `Ring.At.Expansion` / `RowTerms` / `Rows` | 有限多重和による基底展開、行の多重線形性・交代性、`transposeInvariant` |
| `Ring.At.Cofactors` / `Adjugate` | 行・列の余因子展開、`adjugateProduct` と `productAdjugate`、余因子と随伴行列の転置公式 |
| `Ring.At.Adjugate.bumpDeterminant` | 一つの成分への単位の加算に対する \(\det(A+E_{ij})=\det(A)+C_{ij}(A)\) |
| `Ring.At.Operations` | 積の結合則・単位則、逆行列の証明付きの型 `Inverse`、一意性、逆行列の行列式、`basisChange` |
| `Ring.At.Representation` | 線形写像と成分の往復、合成と行列積、線形写像の行列式との一致、逆写像から逆行列の証明を構成 |
| `Ring.At.CommutativeComparison` | `commutative_algebra.Modules.Matrix` との積・転置・恒等行列の一致、逆行列の証明の往復 |
| `Field.At` | `invertibleIff`、非零行列式を持つ行列の型 `Nonsingular` と `inverse`、`componentFormula`、`inverseDeterminant` |

逆行列の成分公式は \((A^{-1})_{ij}=\det(A)^{-1}C_{ji}(A)\) である。
体上で逆行列の存在と行列式の非零性を両方向に証明する。
可換環上では \(\operatorname{adj}(A)A=A\operatorname{adj}(A)=\det(A)I\) を証明する。
基底変更については、証明付きの逆行列 \(Q=P^{-1}\) に対して \(\det(QAP)=\det(A)\) を示す。
転置と随伴行列の比較も同じ行列式から導く。

## 行列族と既存の解析 API

`Topological[K := K, ring := ring].At[n := n]` は `topological_algebra` の行列の積位相を使う。
`determinantContinuous` は任意の位相可換環上での連続性を与える。
`Families[X := X]` は任意の底空間上の成分ごとに連続な行列族を扱い、行列式・余因子の連続性と行列値写像の連続性を構成する。
有限和・有限積の連続性を基底展開に適用して証明する。

`Real.At` と `Complex.At` はそれぞれの体・位相に具体化し、`invertibleOpen` と `inverseContinuous` を公開する。
逆行列写像の定義域には `Nonsingular` の部分空間位相を使う。
`Families.inverseContinuous` は行列式が各点で非零な連続行列族の余因子公式に適用でき、`certifiedInverseContinuous` は与えられた点ごとの逆行列にも適用できる。
スカラーの逆元の連続性は実数・複素数の既存の証明を再利用する。

`Real.At.Smooth[d := d]` は `calculus.MatrixFamily` の標準基底と成分表示を比較する。
`inverseFormula` は既存の線形逆写像と余因子公式の成分が一致することを示し、`smoothFormula` は `calculus.InverseFamily.regular` の滑らかさの証明をその公式へ移す。

## 利用例と検査

[Examples.ref](src/Examples.ref) は零次元の行列式が \(1\) になることと、実二次元の shear 行列 \(\begin{pmatrix}1&t\\0&1\end{pmatrix}\) の行列式・逆行列の存在・逆行列族の連続性を検査する。

```sh
cargo build -p cli --locked
target/debug/cli libs/algebra/matrix_invariants --memory-mib 8192 --cache-stats
```

workspace の共有キャッシュを使い、対象とその全依存パッケージを通常検査する。

対象と依存閉包の検査は成功し、1,205 module を検査、88 module を共有キャッシュから再利用した。
15,635 ソース検査ステップ、最大 RSS 約853 MiB、worker 復旧・重複検査・失われたステップはいずれも0であった。
処理系の変更は含まない。

多項式係数の行列式と随伴行列による Cayley–Hamilton の証明は [polynomial_linear_algebra](../polynomial_linear_algebra/README.md) を参照。
