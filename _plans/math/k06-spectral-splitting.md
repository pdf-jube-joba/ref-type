# K06 連続なスペクトル分離

## 要件

- 主な実装先は `spectral_splitting`。
- 単位円上に固有値を持たない複素行列族について、内側・外側の根群に対応する連続な射影を構成する。
- Bézout 係数と Cayley–Hamilton による不変部分空間分解を、基底変更と可換な形で証明する。
- 束の自己準同型へ局所構成を貼り合わせ、分離された像が部分束になることとホモトピーに沿う比較を示す。

## 依存するタスク

- [K05 代数学の基本定理と根群の連続性](k05-complex-roots.md)
- [Hermitian 行列と連続な局所枠](../../libs/algebra/hermitian_frames/README.md)
- [B03 束の計量・補束と集合による表示](b03-bundle-complements.md)
