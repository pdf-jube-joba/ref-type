# Hermitian 行列と連続な局所枠

実数・複素数上の正定値 Hermitian 形式、Gram–Schmidt、一定階数の直交射影の連続な局所枠と逆座標を扱う。
有限次元は零次元も含み、底空間は任意の位相空間とする。
複素内積は第1引数について共役線形、第2引数について線形である。

## スカラーと共通の正規直交化

代数的な構成は [linear_algebra.Hermitian](../linear_algebra/README.md) と共有する。
`Hermitian.Scalar` は実数の埋め込みと実部、体の共役をまとめ、実数・複素数の実装はそれぞれ `Hermitian.Real.scalar` と `Hermitian.Complex.scalar` にある。
`Hermitian.Over.Inner.Of.Algorithm.exists` は任意の正定値 Hermitian 形式と単射な有限列行列から、正規直交枠、可逆な三角係数行列、分解の等式を構成する。
`Gram.Of` は枠の随伴、像上の逆座標、直交射影とその自己随伴性・冪等性を与える。
既存の実 `Euclidean.Normalization` と `Euclidean.Gram.Step.On.With` もこの構成を使い、既存の滑らかな Gram–Schmidt と接束・法束に接続する。

この package の入口は `Hermitian` である。
`Hermitian.Real.topological` と `Hermitian.Complex.topological` は、それぞれの体の連続演算・共役・実部・実数の埋め込みをまとめる。
`Hermitian.Over[K, field, scalar, topological].At[n]` を以下では `At` と書く。

| module | 公開する内容 |
| --- | --- |
| `At.Matrices` | 共役転置 `adjoint`、二重随伴、`Hermitian` 行列と線形写像の自己随伴性の比較 |
| `At.Matrices.Of` | Hermitian 行列が定める形式と `PositiveDefinite` |
| `At.Forms.Gram` | 任意の正定値形式での `Factorization` とその存在 |
| `At.Forms.Families` | 固定した形式について、任意の底空間上の連続な単射行列族の連続な正規直交化 |
| `At.Forms.Families.Normalize` | 正値ノルムを持つ連続ベクトル族の正規化の連続性 |
| `At.Families.Matrix` | 成分の連続性と固定ベクトル上の連続性の比較、変動するベクトルへの評価 |
| `At.OnProjection.Rank` | 像の代数的な基底による `HasRank`、正規直交 `Frame` と逆座標 |
| `At.Families.ProjectionFrames` | 一定階数の連続な直交射影の、各点の開近傍上の連続な正規直交枠と連続な逆座標 |
| `At.Families.Orthonormalized` | 正規直交化から得る連続な直交射影、階数、局所枠 |
| `At.Square` | [L01](../matrix_invariants/README.md) による正方線形写像の左逆から右逆への証明 |
| `At.Square.Families` | 逆行列族の連続性と可逆な行列を取る点の開性 |
| `At.Unitary` | ユニタリ群の積・逆元・群法則、共役転置による逆元の成分表示、行列の成分から誘導する位相 |
| `At.Unitary.Operations` | 積位相上の積と逆元の連続性 |
| `At.OnProjection` | 像、補射影、相互の消滅と直交分解 |
| `At.Blocks` | ブロック直和の成分・合成・恒等写像、射影と補射影の比較、ユニタリ直和と積の保存 |

`HasRank` の基底は、\(B:K^k\to K^n\) と \(C:K^n\to K^k\) が \(CB=I\)、\(BC=P\) を満たす像の代数的な表示である。
この入力には正規直交性や連続性を要求せず、`frameExists` で正規直交化する。
`ProjectionFrames.exists` は、中心の基底 \(B_0,C_0\) に対して \(C_0P(x)B_0\) の行列式が非零な開近傍を取る。
L01 の逆行列と一定階数性から、その近傍上の基底・逆座標を作り、連続な Gram–Schmidt を適用する。
`Local` は開集合・中心の所属・枠・像上の逆座標と、両写像の連続性を保持する。

## 利用例と検査

[Examples.MovingLine](src/Hermitian/Examples/MovingLine.ref) は列 \((1,z)\) の連続族を正規直交化し、得られる階数1の射影に局所枠の存在定理を適用する。
[実数](src/Hermitian/Examples/Real.ref) と [複素数](src/Hermitian/Examples/Complex.ref) に具体化し、複素ユニタリ群の零次元も検査する。

```sh
cargo build -p cli --locked
target/debug/cli libs/algebra/hermitian_frames --memory-mib 8192 --cache-stats
```

workspace の共有キャッシュを利用し、対象と読み込んだ依存パッケージ全体を検査する。
