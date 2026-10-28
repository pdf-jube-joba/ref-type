# 特異鎖の cap 積

`singular_cap` は整数係数の特異鎖上の cap 積と、その相対版を提供する。`Integral[A, source].At[p, q]` の `map beta` は \((p+q)\)-鎖から \(p\)-鎖への線形写像で、単体の前半を出力し後半に余鎖 `beta` を評価する。`onGenerator` が生成元上の値、`Adjunction.law` が cup 積との評価の随伴を与える。

`Integral.Diagonal.Boundary.Formula.law` は、この約束のもとで
\[
 (\partial c)\frown\beta=\partial(c\frown\beta)+(-1)^p c\frown\delta\beta
\]
を表す。ここで右辺の出力次数は \(p\) である。`Integral.Natural` は連続写像に関する射影公式を与え、`Integral.Pair.Natural` は対写像に関してホモロジー・余コホモロジー上の射影公式を与える。`Integral.Excision` は切除同型とその順写像に関する cap 積の可換式を提供する。`Integral.Unit` は零次の単位余鎖の作用を扱う。

`Integral.Pair.At.Quotient` は相対鎖への絶対余鎖の作用、`RelativeCochain` は相対余鎖と相対鎖から絶対鎖への作用を構成する。両方の境界公式はそれぞれ `Pair.Boundary.Formula` と `Pair.RelativeCochainBoundary.Formula`、相対 cup との随伴は `Pair.At.Adjunction` にある。閉余鎖による作用は `Pair.CohomologyAction` と `Pair.RelativeCohomologyAction` および対応する零次数のモジュールでホモロジー・余コホモロジーへ降下する。

`CochainPair` は相対余鎖の商表示と部分空間上で消える余鎖の表示を比較し、左右の相対 cup 積とその Leibniz 公式、および任意の可換環係数でのコホモロジーへの降下を与える。`CochainPair.Comparison.Cohomology` は相対類から絶対類への写像である。`RelativeEvaluation.With` は任意の整数加群係数で相対 Kronecker 評価を構成する。`External` は絶対外部 cup 積を、`Triple` は二つの部分空間それぞれを保つ鎖・余鎖とコホモロジー上の演算を提供する。

点空間の単位の利用例は [examples/cap](../../examples/cap) にある。個別の通常検査は例えば次で実行できる。

```sh
target/debug/cli libs/topology/singular/cap --module singular_cap.Integral.Pair.At.Adjunction --cache-stats --diagnostics compact
```

二つの部分空間 \(A,B\subseteq X\) が和集合内で開なら、`Triple.Union.Cover.On.Cup` は \(H^p(X,A)\times H^q(X,B)\to H^{p+q}(X,A\cup B)\) を提供する。同じ開被覆条件の下、`CapCohomology*.Transfer` は \(H^q(X,A)\times H_{p+q}(X,A\cup B)\to H_p(X,B)\) を提供する。`Transfer.onSmall` は細分した相対鎖上の作用との一致を示す。正・零次数は `CapCohomology`、`CapCohomologyZero`、`CapCohomologyZeroTarget`、`CapCohomologyZeroZero` で扱う。

`ExternalIntegral.Cup` は射影逆像の和集合に値を持つ相対外部 cup 積を、`ExternalIntegral.Cross.At.Relative` は相対鎖の双線形外積を与える。後者の `onClasses` は代表鎖の通常の外積との一致を示す。`Cross.Boundary` は両正次数と零次数の軸における境界公式を、`Cross.Homology` の `Positive`、`RightZero`、`LeftZero`、`ZeroZero` の各 `Descent` は対応するホモロジー上の双線形外積を提供する。鎖外積の総次数は `singular_products.Cross.degree p q = q + p` の規約に従う。各 `Descent.onClasses` は代表サイクルでの計算規則を与える。 `Cross.Natural.On.ProjectionGeneral` は次数の一致を指定して、対写像の積と相対外積・cap の射影公式を鎖レベルで示す。`Projection` は左因子の次数と同じ次数の余鎖に特殊化した式を与える。`ProjectionPositive`、`ProjectionRightZero`、`ProjectionLeftZero`、`ProjectionZeroZero` は対応するホモロジー・余コホモロジー類の式を与える。

`Cross.Natural` は左右の対写像の積が和集合部分空間を保つことと、相対鎖・相対ホモロジーの外積に関する自然性を示す。`Integral.Pair.ConnectingZeroZero`、`ConnectingZeroPositive`、`ConnectingPositiveZero`、`ConnectingPositivePositive` は閉余鎖による cap とホモロジーの接続写像の整合性を示す。`CochainConnecting.ZeroZeroClasses`、`PositiveZeroClasses`、`PositiveOutputZeroCochain`、`PositiveOutputPositiveCochain` は、余コホモロジーとホモロジーの接続写像に関する cap の符号付き整合性を全非負次数で提供する。正出力次数では結果に \( (-1)^p \) が付く。
`ConnectingPositivePositive.On.Compatibility` は正次数どうしの場合を扱い、閉余鎖に対するホモロジーの接続写像と cap の可換式が全非負次数で揃う。部分空間側の作用は鎖複体の次数移送と零拡張のホモロジー同型を通じて表される。
