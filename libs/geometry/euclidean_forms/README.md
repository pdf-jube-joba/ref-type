# Euclid 空間上の微分形式

`Euclidean[n := n].On[U := U]` は開集合 \(U\subseteq\mathbb R^n\) 上の滑らかな交代形式を扱う。
`Form(k)` の滑らかさは一定引数での評価で定め、`CoefficientSmooth.family` で基底係数から判定できる。

| API | 内容 |
| --- | --- |
| `At[k].space` / `DegreeZero.isomorphism` | ベクトル空間、零次形式と滑らかな関数 |
| `Above[k]` / `coefficientExt` | 次元を超える次数の零性、係数による等式判定 |
| `Wedge` / `Associativity` / `GradedCommutativity` / `UnitLaws` | shuffle 外積と法則 |
| `Partial` / `ExteriorDerivative` / `Square` / `Leibniz` | \(d\omega=\sum_i dx^i\wedge\partial_i\omega\)、\(d^2=0\)、Leibniz 則 |
| `FunctionDifferential.law` | 零次の外微分と全微分の一致 |
| `DeRham` / `DeRham.At` | 自然数・整数次数の複体、閉形式・完全形式の商 |
| `DeRham.DegreeZero` | \(df=0\) の関数との同型 |
| `CoordinateBasis.At.Enumeration` / `Differential.formula` | 有限基底、係数からの復元と外微分公式 |

`Euclidean.Pullback[m, U, V, f]` はヤコビアンによる引き戻し、`Identity`・`After` は恒等・合成則を返す。
`Pullback.Product`・`DegreeZero` は外積・零次の外微分との整合性を示す。
`Evaluation` は滑らかな可変引数での評価、`Gluing` は開被覆上の貼り合わせを扱う。
`Restriction` は包含に沿う制限と偏微分・積・外微分の可換性を持つ。
`Regrade[k,l].cast` は集合値の移送、`RegradeIdentity` と `composition` はその法則、`bridge` はリスト表示による移送との一致を返す。
