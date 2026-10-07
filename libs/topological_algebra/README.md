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
| `Coordinates.Update` | 一成分の置換、置換の法則と連続性。 |
| `Real` | 実数直線の位相的加法群と位相的可換環。 |
| `Complex` | 実数直線の二因子積による複素数の位相。 |
| `Complex.Functions` / `Complex.Ring` | 実部・虚部、和・負号・積・共役・絶対値・実数倍・非零逆数の連続性と位相的可換環。 |
| `Matrix` | 行・列の二重座標空間としての行列位相と成分の連続性。 |
| `Matrix.Universal` | 行列族の全成分の連続性から行列値写像の連続性を導く定理。 |
| `Matrix.Operations` / `Matrix.Operations.Composition` | 和・負号・スカラー倍・転置の連続性と、有限添字列上の行列積の連続性。 |
| `FiniteDimensional.Over.Functions` | 位相的スカラー環に値を持つ関数の有限和の連続性。 |
| `FiniteDimensional.Over.Space` | 基底による有限次元空間の位相、座標写像の同相。 |
| `Space.Functional` / `Space.Linear` / `Space.Comparison` | 線形汎関数・有限次元線形写像の連続性、基底を変えた恒等写像の同相と位相の一致。 |

座標位相は添字集合の有限性や列挙の選択を要求しない。
有限次元の円板・球面は `algebraic_topology.Euclidean.Dimension` がこの構成を使う。
行列の位相は `linear_algebra` の関数による行列表現と同じ台集合を使う。

`Space` は `FiniteDimensional.Over.Space` の具体化を指す。
`Over` の parameter は体の構造であり、連続性の仮定は各定理で量化する。

[行列の利用例](../../tests/projects/topological-k-theory/src/Matrix.ref) は実数・複素数の位相的環と複素行列の積を検査する。
[有限次元空間の利用例](../../tests/projects/topological-k-theory/src/Finite.ref) は実数上の線形写像・座標同相・基底変更を検査する。

有限座標空間のコンパクト性は、二因子積の定理の具体化が [G06](../../_plans/gaps.md#g06) の型の不一致で失敗するため、ここで実装を停止している。

```sh
target/debug/cli libs/topological_algebra --no-cache --diagnostics compact
target/debug/cli tests/projects/topological-k-theory --no-cache --diagnostics compact
```
