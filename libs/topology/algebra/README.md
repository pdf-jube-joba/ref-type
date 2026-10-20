# 位相と代数の接続

スカラー・座標空間・行列空間の連続性を成分ごとの条件に帰着する。

| module | 内容 |
| --- | --- |
| `Topology` / `Topology.Functions` | 位相的可換群・環と連続関数の演算 |
| `Coordinates` / `Universal` / `Update` | 任意の添字集合の積位相、普遍性、一成分の置換 |
| `FinitePower` | コンパクト空間の有限積のコンパクト性 |
| `Euclidean.Dimension.Completeness` | 最大値距離に関する有限座標空間の完備性、成分ごとの極限 |
| `Real` / `Complex` / `Complex.Functions` / `Complex.Ring` | 実数・複素数の位相と演算の連続性 |
| `Matrix` / `Universal` / `Operations` / `Operations.Composition` | 二重座標による行列位相、成分判定、和・転置・有限行列積 |
| `FiniteDimensional.Over.Functions` | 位相的スカラー環に値を持つ関数の有限和 |
| `FiniteDimensional.Over.Space` / `Space.Functional` / `Space.Linear` / `Space.Comparison` | 基底による有限次元位相、座標同相、線形写像の連続性、基底変更による位相の一致 |

座標位相の添字集合は有限性や列挙を要求しない。
行列の台集合は `linear_algebra` の関数による表現を使う。
`Over` の parameter は体の構造で、連続性は定理の仮定として量化する。

利用例は[行列](../examples/cells/src/Matrix.ref)と[有限次元空間](../examples/cells/src/Finite.ref)を参照。
