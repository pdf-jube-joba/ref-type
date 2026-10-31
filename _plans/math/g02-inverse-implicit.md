# G02 逆関数・陰関数と正則値の局所形

## 要件

- 主な実装先は `inverse_implicit`。
- 有限次元の逆関数定理を近傍と逆写像の存在を含めて証明する。
- パラメータ付き陰関数定理と一定階数定理を証明し、正則値の逆像の局所座標を構成する。
- 多様体の写像の正則値から部分多様体と接空間の核の同定を構成する。

## 依存するタスク

- [L01 行列式と可逆行列](../../libs/algebra/matrix_invariants/README.md)

## 実装

[inverse_implicit](../../libs/geometry/inverse_implicit/README.md) が滑らかな有限次元写像について各項目を実装する。

| 要件 | 公開 API |
| --- | --- |
| 近傍と逆写像の存在を含む逆関数定理 | `Euclidean.InverseFunction.localExistence` と `LocalInverse` |
| パラメータ付き陰関数定理 | `Product.Implicit.localExistence` と `Solution` |
| 定階数定理 | `Rank.Witness`、`ConstantRank.On.localExistence` と両側の座標変換を持つ `NormalForm` |
| 正則ファイバーの局所座標 | `Product.Submersion.localExistence`、`LocalFiber` |
| 多様体の正則値部分多様体と接空間の核 | `Product.RegularValue.Of.manifold`、`Smooth.embedding`、`Smooth.At.identificationExists` |

[利用例](../../libs/geometry/inverse_implicit/src/Examples.ref) は非線形な shear、陰関数、階数一の非線形写像、放物線の正則値部分多様体と接空間の核、零次元を具体化する。
