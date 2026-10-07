# 位相と代数の接続

スカラー・座標空間・行列空間に位相を与え、連続性を成分ごとの条件に帰着する。
直接依存は `std`、`real`、`complex`、`algebra`、`linear_algebra`、`topology` である。
公開 module は [root.ref](src/root.ref) にある。

| module | 構成と証明 |
| --- | --- |
| `Topology` | 位相的可換群と位相的可換環のデータ・演算法則。 |
| `Topology.Functions` | 連続関数の和・逆元、位相的可換環を値域とする関数の積の連続性。 |
| `Coordinates` | 任意の添字集合について、評価写像の逆像で生成する積位相。 |
| `Coordinates.Universal` | 全成分の連続性から座標空間への連続性を導く普遍性。 |
| `Real` | 実数直線の位相的加法群。 |
| `Complex` | 実数直線の二因子積による複素数の位相。 |
| `Complex.Functions` | 実部・虚部、和、共役の連続性。 |
| `Matrix` | 行・列の二重座標空間としての行列位相と成分の連続性。 |
| `Matrix.Universal` | 行列族の全成分の連続性から行列値写像の連続性を導く定理。 |

座標位相は添字集合の有限性や列挙の選択を要求しない。
有限次元の円板・球面は `algebraic_topology.Euclidean.Dimension` がこの構成を使う。
行列の位相は `linear_algebra` の関数による行列表現と同じ台集合を使う。

[利用例](../../tests/projects/topological-k-theory/src/Matrix.ref) は二行二列の複素行列族を構成し、共役の連続性を成分判定へ接続する。

```sh
target/debug/cli libs/topological_algebra --no-cache --diagnostics compact
target/debug/cli tests/projects/topological-k-theory --no-cache --diagnostics compact
```
