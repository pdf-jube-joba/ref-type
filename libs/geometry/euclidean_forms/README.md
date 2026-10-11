# Euclid 空間上の微分形式

局所微分形式、外積・外微分、座標表示、引き戻しを扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`Euclidean[n := n].On[U := U]` は開集合 \(U\subseteq\mathbb R^n\) 上の滑らかな微分形式を扱う。
`Form(k)` は各点での交代 \(k\)-形式の族であり、一定の引数で評価した関数が滑らかである。
`CoefficientSmooth.family` は標準基底での係数の滑らかさから、この条件を導く。
`coefficientExt` は基底係数の一致による形式の等式判定を提供する。

| API | 構成と法則 |
| --- | --- |
| `At[k].space` | 和と実数のスカラー倍によるベクトル空間 |
| `DegreeZero.isomorphism` | 零次形式と滑らかな実数値関数の線形同型 |
| `Above[k]` | \(k>n\) の形式の零性 |
| `Wedge[p, q].apply` | 点ごとの符号付き shuffle による外積と双線形性 |
| `Partial[k].apply` | 係数の偏微分、線形性、混合偏微分の交換 |
| `ExteriorDerivative[k].apply` | \(d\omega=\sum_i dx^i\wedge\partial_i\omega\) |
| `Square[k].law` | \(d^2=0\) |
| `Associativity` / `GradedCommutativity` / `UnitLaws` | 次数をそろえた外積の結合則・次数付き可換則・単位則 |
| `Leibniz[p, q].law` | 次数付き Leibniz 則 |
| `FunctionDifferential.law` | 零次の外微分と全微分の一致 |
| `DeRham.complex` | 実加群の余鎖複体 |
| `DeRham.integerComplex` | 負次数を零空間へ拡張した整数次数の複体 |
| `DeRham.DegreeZero.isomorphism` | \(df=0\) の滑らかな関数と零次コホモロジーの線形同型 |
| `DeRham.At[k]` | 閉形式・完全形式・商コホモロジー・類の消滅判定 |

`Euclidean.Pullback[m, U, V, f]` は滑らかな写像 \(f:U\to V\) のヤコビアンによる前合成から引き戻しを構成する。
`Pullback.After.law` は合成則、`Euclidean.Identity.law` は恒等写像の引き戻しの恒等則を証明する。
`Pullback.DegreeZero.law` は零次で外微分と引き戻しが可換になることを証明する。
`Euclidean.Gluing` は開被覆上の互換な局所形式から一意な貼り合わせを構成する。
`Pullback.At[k].map` は線形写像、`Pullback.Product[p, q].law` は外積との整合性を返す。
`Euclidean.Evaluation[m, U]` は基底係数と引数ベクトルの各座標が滑らかなとき、可変の引数での評価が滑らかになることを証明する。

`Euclidean.Restriction[U, V]` は \(U\subseteq V\) に沿う形式の制限を構成する。
`At[k].partial`、`Product[p, q].law`、`Differential[k].law` は制限と偏微分・外積・外微分との可換性を表す。
等しい次数間の移送には、集合値の `\idelim` による `Regrade[k, l].cast` を用いる。
`RegradeIdentity[k].law` は `\transporteq` による自己移送の恒等則、`Regrade[k, l].composition` は移送の合成則を返す。
リスト上の成分表示からの復元は `RegradeDisplay[k, l].convert` に置き、`Regrade[k, l].bridge` は次数の等式の下で `cast` との一致を証明する。

`Euclidean.On.CoordinateBasis` は座標一形式の外積を任意次数で構成する。
`CoordinateBasis.At[k].Enumeration` は増加添字列の重複のない有限列挙であり、`reconstruction` は滑らかな基底係数からの復元、`Differential.formula` は外微分の係数公式を返す。

検査方法と関連パッケージは [ライブラリ一覧](../../README.md) を参照。
