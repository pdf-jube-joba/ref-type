# 可換環上の加群

Hom とテンソル積、射影性、有限自由加群の行列を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

| module | 公開する内容 |
| --- | --- |
| `commutative_algebra.Modules.Matrix` | 有限自由加群の準同型と行列の往復、積と合成、転置、恒等行列、逆行列と加群同型の対応。 |
| `commutative_algebra.Modules.Elementary` | 行交換、異なる行の整数倍の加算、符号反転の加群同型と逆行列の証明。 |
| `commutative_algebra.Modules.HomSpace` / `FreeHom` | 準同型の加群構造と \(\operatorname{Hom}_R(R^{(S)},A)\cong A^S\)。 |
| `commutative_algebra.Modules.Tensor.Adjunction` | テンソル積の双線形な普遍性と Hom–tensor の加群同型。 |
| `commutative_algebra.Modules.ProjectiveTensor`、`ProjectiveTensorShortExact` | 射影加群とのテンソル積による単射性・短完全列の保存。 |
| `commutative_algebra.Modules.TensorProjective` | 二つの射影加群のテンソル積の射影性。 |

検査方法と関連パッケージは [ライブラリ一覧](../README.md) を参照。
