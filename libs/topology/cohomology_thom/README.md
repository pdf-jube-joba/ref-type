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

`RelativeSuspension.On[A, source, subset].Covering.With[M].At[z].isomorphism` は円柱対
\((I\times A,\partial I\times A\cup I\times B)\) の相対コホモロジーを1次数ずらす同型である。
開被覆は時刻が1未満・0より大きい二つの部分で、各部分対の変形収縮と共通部分対の比較を明示的に構成する。

`LocalDisk.On[X, source].With[M].isomorphism n z` は
\(H^z(X;M)\cong H^{\operatorname{shift}(n,z)}(X\times D^n,X\times\partial D^n;M)\) を与える。
`shift` は整数次数に後続操作を \(n\) 回適用する。
`With.Negative[n, k].zero` は負の底次数から得られる相対群の消滅を示す。
`Ring[R, ring].Rank[n].localClass` はこの加法的比較による単位類の像で、`coordinateOfClass` と `unique` がその正規化を特徴付ける。

`RelativePullback.On.To.Along.Cup.Cohomology.naturality` は対写像に対する相対 cup 積の自然性を与える。
`Thom.Real.For.With.Pullback[Y, source, f, regular].Ring[R, ring]` は実際の引き戻し束と引き戻し計量を用いる。
`Product[p, n].law` と `Degree[n].Euler.law` はそれぞれ積および零切断像と引き戻しの可換式である。

`RelativeMayerVietoris.OpenCover.On.With.Coordinates.Cohomology[z].law` は列の制限写像を通常の二つの対写像による制限と同定する。
`Coordinates.Difference[z].law` は次の写像を共通部分への制限の差と同定する。
`Cohomology.Gluing[z].Ordinary` は通常の制限が一致する二つの局所類から、共通部分の直前の群の消滅を用いて一意な貼り合わせを構成し、`left`、`right`、`unique` を公開する。

`CoefficientChange.OnSpace[A, source, R, S, ring, targetRing].Morphism` は整数線形な係数写像と積・単位の保存からなる環準同型である。
`With[morphism].Cup.Cohomology.law` と `Relative[subset].Cup.Cohomology.law` は絶対・相対 cup 積との整合性を示す。
`Unit.law`、`Along.Degree.law`、`Relative.Degree.Forget.law` はそれぞれ単位類、空間の引き戻し、相対条件を忘れる写像との可換式である。
`RelativeMayerVietoris.OpenCover.On.ChangeCoefficients.At.law` と `RelativeSuspension.On.Covering.ChangeCoefficients.At.law` は接続写像および相対懸垂同型の係数変更自然性を示す。

`RelativeMayerVietoris.OpenCover.On.Product[K, ring].Cup[p, q]` は小さい相対余鎖に対する cup 積を構成する。
その `Compare.law` は通常の相対余鎖の制限との一致を、`Differential.law` は左因子が閉じている場合の符号付き Leibniz 公式を示す。
`Product.Positive[p, q]` は右因子が正次数の場合にコホモロジーへ降下する。
`Product.Connecting[p, q].Whole.law` は通常の相対 Mayer–Vietoris 接続写像に対する \(\delta(a|_{U\cap V}\smile b)=(-1)^p a\smile\delta b\) を与える。


`RelativeSuspension.On.Covering.Product[K, ring].Cup[p, q].law` は相対懸垂と cup 積の符号付き比較を与える。
`LocalDisk.On.Step[n].Product[K, ring, p, q].Base.onClasses` は円板の次数上昇を底空間からの引き戻しと比較する。

`LocalDisk.On[X, source].Ring[R, ring].canonical n` はランク0の相対単位類から相対懸垂と円板同相で再帰的に構成した類である。
`thomIsomorphism n p` は任意のランクと可換係数環について
\[
H^p(X;R)\longrightarrow H^{p+n}(X\times D^n,X\times\partial D^n;R),\qquad
 a\longmapsto\pi^*a\smile\operatorname{canonical}(n)
\]
を順写像とする \(R\)-加群同型である。
ランク0では空の境界を忘れる同型と円板の射影を用い、後続ランクでは円板の次数上昇同型と符号の対合性から単射性と全射性を帰納的に証明する。

`LocalDisk.On.Change[K, L, ring, targetRing, morphism].canonical n` は係数環の単位的準同型が全ランクの局所 Thom 類を保つことを示す。
`LocalDisk.On.Step.ChangeCoefficients.law` は円板の次数上昇同型と係数加群の変更の自然性を与える。

`RelativeMayerVietoris.OpenCover.On.From.Along.With.Ordinary[z].law` は被覆を保つ対写像に対する通常の相対接続写像の自然性を与える。
`RelativeSuspension.On.From.With.At[z].law` は相対懸垂同型と対写像の引き戻しの可換性を示す。

`LocalDisk.On.From.Ring.canonical n` は連続な底写像による局所 Thom 類の引き戻しの自然性を与える。
`From.Ring.Degree[n, p].law` は cup 積による局所 Thom 同型と引き戻しの可換性を示す。

`LocalDisk.Point[K, ring].Rank[n]` は一点上の円板対の生成元と係数加群との同型を与える。
`LocalDisk.On.Ring.Top[n]` は次数0からの正規化同型と点での評価座標を公開する。
`Ring.Fibers[n].Fiber[x]` は実際の円板対の写像によるファイバー制限を構成し、`value` が評価座標との一致を示す。
`Fibers.detectedOnFibers` と `uniqueNormalized` はファイバー上の生成元による局所 Thom 類の一意性を示す。
`RelativePullback.On.To.Homeomorphism.Degree[n].isomorphism` は対の同相に対する係数環上の線形同型である。

`Thom.Real.For.With.Chart[c]` は実際の束の局所自明化から標準円板対への動径同相を構成する。
`Chart.Ring.Degree[p].isomorphism` と `formula` は cup 積による局所 Thom 同型を与える。
`Chart.Open` は制限束の円板対を元の円板束のチャート対応開部分へ同定する。
その `Ring.Degree[p].isomorphism`、`formula`、`Additive.below` は開部分上の同型と直前次数の消滅を公開する。

`RelativeMayerVietoris.OpenCover.On.RightAction[K, ring]` は空の対の列から相対列への、固定した右因子との cup 積を構成する。
`Cup.SumAction.projection`、`Cup.Differential.law`、`Cup.Addition.law` は射影、微分、加法との整合性を示す。
`Positive.linear` は境界保存による正次数のコホモロジー写像であり、`Connecting.law` は接続写像との比較を次数の移し替えを含めて与える。

`RightAction.Cup.Compare.Cohomology` は小さい余鎖上の積を通常の相対 cup 積と同定する。
`RightAction.Positive.Compare.law` と `Connecting.Whole.law` は次数の移し替えを含むコホモロジー・接続写像の比較を与える。
`RelativeMayerVietoris.OpenCover.On.Cohomology.Vanishing[z].whole` は二つの部分と共通部分の直前次数の消滅から全体の消滅を示す。
`Thom.Real.For.With.Coefficients.ProjectionIso[p]` は円板束の射影による絶対コホモロジー同型を公開する。
`Chart.Open.Ring.Degree[p].ordinaryIsomorphism` は開円板対の絶対コホモロジーからの cup 同型であり、`Chart.Open.Additive.Negative[k].zero` はランク未満の全次数の消滅を与える。

`RelativeAction[A, source, subset, K, ring].Degree[p, q]` は空の境界を持つ相対群から、固定した相対類との右 cup 積を取る写像を与える。
`integerMap` と `ringMap` は同じ写像の整数線形・係数環線形な構造で、`Along.Degree.law` は対写像による引き戻しとの可換性を示す。

`RelativeMayerVietoris.OpenCover.On.RightAction.Native[p, q]` は通常の相対群における制限・差写像の cup 積比較図式を構成する。
`Diagram` はこの図式の次数をまとめて移すための構造であり、`Five` は Mayer–Vietoris 列から実際の五項完全列を構成する。
`Gluing[p, q].With[u].isomorphism` は左右と共通部分での局所同型から、次数 \(p+1\) における cup 積の同型を導く。
`Zero[q].With[u].isomorphism` は直前の共通部分の群の消滅を用いて次数0を扱う。

`Thom.Real.For.With.Chart[c].Restrict[U, open, contained].chart` は元のフレームを小さい開集合へ制限した実際の束チャートを構成する。
`Chart.Fiber[x].fiberPair` は元の円板束の実ファイバーと、一点上の標準円板対との同相を与える。
`Fiber.Ring[K, ring].generator` はこの同相で運んだ生成元で、`isomorphism` と `normalized` が係数環の1による正規化を示す。
`Fiber.Ring.Normalization.normalized` はチャート上の Thom 類のファイバー制限がこの生成元であることを示す。
`Open.Ring.Fibers.detected` は実ファイバーへの制限が局所類を共同で検出することを示す。

`Thom.Real.For.With.Atlas.existsFiniteCW` は、実際の有限 CW 構造のコンパクト性から有限個の束チャートの定義域による被覆を得る。

`Thom.Real.For.With.Local[K, ring].Rank[n].Orientation.SignedOrientation` は実ファイバーの相対類と、その類が局所チャートの正規化された生成元またはその負に一致することからなる向きのデータである。
チャートの次元は \(n\) と一致し、符号付き局所類は実際の円板対の構成から得る。
小さい開集合への制限でファイバー値が保存されることを証明し、有限 CW 構造のコンパクト性から、このデータと整合する有限被覆を取る。
空集合からの有限帰納法で、類・ファイバーによる検出・ランク未満の消滅・cup 同型を同時に貼り合わせる。

`Thom.Real.For.With.Oriented[K, ring, n, orientation, complex]` は有限 CW 底空間上の大域的な公開入口である。

| API | 内容 |
| --- | --- |
| `class` | \(H^n(D(E),S(E);K)\) の大域 Thom 類。 |
| `normalized` | 元の円板束の各実ファイバーへの制限が指定された類と一致する。 |
| `uniqueNormalized` | 同じファイバー値を持つ相対類の一意性。 |
| `Degree[p].isomorphism` | \(H^p(X;K)\cong H^{p+n}(D(E),S(E);K)\)。順写像は実際の \(a\mapsto\pi^*a\smile u\)。 |
| `euler` | 零切断への Thom 類の引き戻し。 |
| `Degree[p].zeroSection` | Thom 同型の像を零切断へ引き戻すと Euler 類との積になる。 |
| `Below[k].zero` | \(\operatorname{shift}(n,-k-1)\) 次の相対群の消滅。 |

`Local.Rank[n].Fiber[x].Generator` は、係数環から実ファイバーの最上次相対群への加群同型が1をその類へ送ることを表す。
`Orientation.generates` は符号付きチャートの局所整合性から、向きが指定する各ファイバー類が実際に生成元であることを示す。

`Thom.Real.For.With.ModTwo[n, constantRank, complex]` は向きを引数に取らない。
`algebra.Two` の二元体上では実ファイバーの生成元が一意であることを証明し、その一意な生成元を各ファイバーで選ぶ。
正規化された局所チャートの類がこの選択と一致するため、有限 CW 底空間上で `class`、`euler`、`Degree[p].isomorphism` を構成できる。
`normalized` と `uniqueNormalized` は元の円板束の実ファイバーに関する正規化と一意性を与える。

`CoefficientChange.FromIntegers[K, ring]` は整数加群の1へのスカラー作用から \(\mathbb Z\to K\) を構成する。
`linear`、`multiply`、`unit` が加法・積・単位の保存を証明し、`OnSpace[A, source].morphism` は任意の係数環への標準係数変更を与える。

`Oriented.Change[L, targetRing, morphism]` は元のファイバー生成元を係数写像で送り、同じチャートと符号で変更後の向き `targetOrientation` を構成する。
`classLaw` は大域 Thom 類の係数変更、`Degree[p].law` と `inverseLaw` は Thom 同型の両方向の可換式、`eulerLaw` は Euler 類の係数変更を与える。
局所標準円板の生成元から実際の計量ファイバーへの比較を経て、変更後の大域類の一意性を用いて証明する。

`Thom.Real.For.With.Integral[n, orientation, complex]` は整数係数の公開入口である。
`Coefficients[K, ring]` は標準準同型 \(\mathbb Z\to K\) による向きと Thom 類の変更、および Thom 同型と Euler 類の比較を与える。
`Oriented.Integer.isomorphism z` は任意の整数次数で
\(H^z(X;K)\cong H^{\operatorname{shift}(n,z)}(D(E),S(E);K)\) を与える。
非負次数では実際の cup 積による同型を整数加群へ制限し、負次数では両群の消滅を用いる。

`Additive[M].Degree[z].forget` と `sphereRestriction` は円板・球面対の長完全列の二つの写像を公開する。
`forgetCycles` と `forgetOnClass` は前者を余鎖の代表元で計算する。
`Coefficients[R, ring].SphereSequence.Sphere.homeomorphism` は実際の球面束と円板束の境界部分空間を同定し、`isomorphism z` は境界部分の整数次数コホモロジーから球面束のコホモロジーへの同型である。
`SphereSequence.zeroSectionAt z` は相対条件を忘れて零切断で引き戻す整数線形写像で、`Natural[t].law` が非負次数で通常の零切断写像との一致を示す。
`SphereSequence.Functor.At[z].law` は整数次数の引き戻しが合成を保つことを示す。

`Oriented.Reverse.reversed` は各ファイバー生成元と局所チャートの符号を反転した実際の向きを構成する。
`classLaw` と `eulerLaw` は Thom 類と Euler 類の符号反転を、`Degree[p].law` と `inverseLaw` は Thom 同型の両方向の符号反転を与える。
`ModTwo.Compare[given].classLaw` は任意の符号付き mod 2 向きから得られる類と標準 mod 2 類の一致を示す。
`Integral.ModTwo.classLaw` と `eulerLaw` は整数類の標準係数変更が標準 mod 2 類と一致することを示す。

`Oriented.Gysin.Degree[z].sequence` は実際の球面束について、整数次数の五項完全列
\[
H^z(X;R)\xrightarrow{\smile e}H^{z+n}(X;R)
\xrightarrow{\pi^*}H^{z+n}(S(E);R)
\xrightarrow{\pi_!}H^{z+1}(X;R)
\xrightarrow{\smile e}H^{z+n+1}(X;R)
\]
を公開する。
列の群と写像は整数加群として表し、次数 \(z+n\) は `LocalDisk.shift n z` で実装する。
`cupEuler`、`pullback`、`integration`、`higherCupEuler` が四つの写像である。
`Positive[p].law` は非負の底次数で最初の写像を Euler 類との cup 積と同定し、`Negative[k].law` は負の底次数を扱う。
`Degree[z].higherLaw` は最後の Euler 項の次数の移し替えを与える。
`Degree[z].Pullback.law` は二番目の写像が球面束の実際の射影による引き戻しであることを示す。
`Integral.Gysin` と `ModTwo.Gysin` はそれぞれ整数係数と標準 mod 2 類に対する入口である。

`Pullback.Fiber[y].Ring[K, ring].Degree[n].law` は引き戻し束の実ファイバー制限と元の束の実ファイバー制限の可換式である。
`Pullback.Ring.Chart[c].Fiber[y].generator` は引き戻した実チャートの標準生成元が元の生成元の引き戻しに一致することを示す。
局所制限束に入る輸送を明示的に比較した上で、動径同相による座標写像の可換性を証明する。
`Pullback.Ring.Oriented[n, orientation, complex, sourceComplex].pulledOrientation` はこのファイバー写像から引き戻し束の符号付き向きを構成する。
`classLaw`、`eulerLaw`、`Degree[p].law` と `inverseLaw` はそれぞれ大域 Thom 類、Euler 類、Thom 同型の順方向と逆方向の自然性を与える。
`Pullback.ModTwo[n, constantRank, complex, sourceComplex]` は引き戻し束の標準 mod 2 類との比較を公開する。

`MixedCup[A, source, first, second, K, ring].Cup[p, q].Both.Cohomology` は二つの相対余鎖の cup 積を、両部分で消える余鎖の複体へ降ろす。
`Union.Cover.On[conditions].Cup[p, q].apply` は、二つの部分が和集合内で開いているとき、通常の \(H^p(A,\mathrm{first};K)\otimes H^q(A,\mathrm{second};K)\to H^{p+q}(A,\mathrm{first}\cup\mathrm{second};K)\) を構成する。
`bilinear` は基礎の整数加群に関する双線形性で、`CommonIso.Cohomology.Canonical.law` が小さい鎖との比較を通常の余鎖による写像と同定する。
鎖と開被覆の幾何は `singular_cap.Triple` を再利用し、係数と cup 積は指定された可換環を使う。

`RelativeDisk.On[X, source, subset].With[M].isomorphism n z` は底空間の部分も相対化した円板の同型
\(H^z(X,B;M)\cong H^{z+n}(X\times D^n,X\times\partial D^n\cup B\times D^n;M)\) を構成する。
全ランクの相対懸垂から構成し、`From.With.law` は底空間の対写像に関する自然性を与える。
`Thom.Real.For.With.Shell` は円板束の \(\|v\|>1/2\) という開部分と、零切断を固定する連続写像 `clip` を与える。
`Shell.Over[U].equivalence` は球面境界に底空間部分 \(U\) を加えた対と、開いた殻に同じ部分を加えた対の実際の対ホモトピー同値である。
