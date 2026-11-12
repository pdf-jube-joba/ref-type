# Thom 相対コホモロジーの演算

`Thom.Real.For[X, F, bundle].With[metric]` は実計量束の実際の円板・球面対を使う。
`Coefficients[R, ring]` は可換環係数、`Additive[M]` は整数加群係数の入口である。

| API | 内容 |
| --- | --- |
| `Coefficients.Degree[n].Class` | 円板・球面対の相対コホモロジー。 |
| `Coefficients.Product[p, n].linear u` | 指定した相対類 \(u\) による \(a\mapsto\pi^*a\smile u\) の線形写像。 |
| `Coefficients.Product.Forget.law` | 相対条件を忘れる写像と cup 積の整合性。 |
| `Coefficients.Product.ZeroSection.law` | \(s^*(\pi^*a\smile u)=a\smile s^*u\) の零切断公式。 |
| `Coefficients.Product.addClass` / `scaleClass` | 相対類の加法・スカラー倍に対する積の公式。 |
| `Coefficients.Degree[n].zeroSection` | 相対類を絶対類へ送り、零切断で引き戻す線形写像。 |
| `Coefficients.Degree[n].euler u` | 指定した相対類の零切断への引き戻し。 |
| `Additive.Degree[z].thomComparison` | Thom 商の被約コホモロジーから円板・球面対への同型。 |
| `Additive.Degree[z].diskComparison` | 円板束の収縮による底空間とのコホモロジー同型。 |
| `Additive.Degree[z].connecting` | 円板・球面対の長完全列の接続写像。 |
| `Fiber[x].Additive[M, z].restriction` | 実際の円板ファイバーとその球面への相対制限写像。 |

`Thom.StandardFiber[n].With[M]` は実次元 \(n+1\) の標準円板・球面对の最上次コホモロジーを係数加群と同定する。
`lift` と `coordinate` はその両方向の線形写像で、`unique` は指定された座標を持つ類の一意性を示す。
`Integral.generator` は座標1の整数類であり、`reverseCoordinate` はその負の類の座標を計算する。

`Thom.Real.For.Change[left, right].Additive[M, z].isomorphism` は計量変更の円板同相が球面境界を保つことから得られる相対コホモロジーの同型である。
