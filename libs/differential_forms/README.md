# 微分形式

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
等しい次数間の移送には、リスト上の表示を保存して形式を復元する `Regrade[k, l]` を用いる。

`Euclidean.On.CoordinateBasis` は座標一形式の外積を任意次数で構成する。
`CoordinateBasis.At[k].Enumeration` は増加添字列の重複のない有限列挙であり、`reconstruction` は滑らかな基底係数からの復元、`Differential.formula` は外微分の係数公式を返す。

`Forms[n].On[M].Form(k)` は最大アトラスの全チャートに局所形式を割り当て、重なり上で引き戻しが一致する族である。
`At[k].space`、`Wedge`、`ExteriorDerivative`、`Square`、`Leibniz` は大域形式のベクトル空間と外代数・外微分の法則を公開する。
`Pointwise[k]` は接空間上の滑らかな交代形式の族との双方向の対応であり、`leftInverse` と `rightInverse` は往復の一致を示す。
`DegreeZero` は大域零次形式を滑らかな関数と結ぶ。

`Pullback[n, m].Between[M, N].Of[f]` は一般の滑らかな写像による引き戻しを構成する。
`At[k].map`、`Product[p, q].law`、`Differential[k].law` は線形性・外積・外微分との整合性を返す。
`PullbackIdentity` と `PullbackComposition` は形式とコホモロジーの恒等則・反変な合成則を示し、`PullbackDiffeomorphism` は両者の同型を返す。
`Restriction` と `Gluing` は任意の開被覆に沿う制限・一意な貼り合わせを公開する。
`Gluing.On.Cover[I, domains].Piece[i]` は被覆の各開部分多様体と、その `Form(k)` を返す。
`At[k, forms].Compatible` は包含写像の微分で共通の接空間へ移した局所形式の一致を表し、`apply` は被覆と互換性の証明から大域形式を構成する。
`AtlasForms` は小さいアトラス上の互換な族を最大アトラスへ一意に拡張し、形式とコホモロジーの同型を構成する。
`Presentation` は同じ最大アトラスを持つ二つの表示を標準的な同型で結ぶ。

`Forms.On.DeRham` は外微分から余鎖複体と商コホモロジーを構成する。
`At[k]` は閉形式・完全形式・類と等式判定を、`Product` とその法則は商の代表によらない次数付きの積を公開する。
`DeRham.DegreeZero.isomorphism` は零次コホモロジーと微分が零になる滑らかな関数の線形同型である。
具体例は [manifolds-de-rham project](../../tests/projects/manifolds-de-rham/src/root.ref) にある。

```sh
target/debug/cli libs/differential_forms --no-cache --diagnostics compact
```
