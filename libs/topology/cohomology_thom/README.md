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

`RelativeMayerVietoris.OpenCover[A, source, subset].On[cover].Cohomology[coefficients].At[z]` は、開被覆に対する実際の相対特異コホモロジーの Mayer–Vietoris 列を与える。
`restriction`、`difference`、`connecting` と、各項での `exactAtSum`、`exactAtIntersection`、`exactAtWhole` を公開する。
境界部分に含まれない特異単体の自由加群基底から、小さい相対鎖の分裂短完全列を構成する。
任意の整数加群への Hom を取り、小さい鎖との比較および直和との比較を通じて通常の相対コホモロジーへ移す。

`Cohomology.Gluing[z]` は両開集合の整合する類の貼り合わせの存在を示し、直前の次数の共通部分の相対コホモロジーが消える場合に一意な `glue` を構成する。
`Thom.Real.For.With.ChangeCoefficients[M, N, u].Degree[z].map` は係数加群の準同型による変更で、`Fiber[x, z].law` はファイバー制限との自然性を示す。
`CoefficientChange.On[C, M, N, u].Along[D, f].At[z].law` はその一般の鎖写像に対する自然性である。

`Thom.Real.For.With.ZeroRank[rankZero].Ring[R, ring]` はランク0の束の Thom 類 `class` を構成する。
`Degree[p].isomorphism` の順写像は \(a\mapsto\pi^*a\smile u\)、逆写像は零切断への引き戻しである。
`euler` はこの Thom 類の Euler 類が単位類であることを示す。
`ZeroRank.With[M, z].isomorphism` は任意の整数加群係数と整数次数で底空間のコホモロジーへの比較を与える。
