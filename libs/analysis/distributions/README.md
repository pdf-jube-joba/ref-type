# 分布と弱微分

Dedekind 実数上の Euclid 空間の試験関数、分布、局所可積分関数と弱微分を扱う。
入口は `distributions.Euclidean[n]` で、次元零も含む。

## 試験関数と連続双対

`Test` は既存の `lp_spaces.Euclidean[n].SmoothCompact` と同じ集合である。
`TestOperations` は加法、スカラー倍、偏微分、点ごとの積と任意階の `jet directions test` を構成する。
微分は実際の偏導関数であり、台の包含、線形性、混合偏微分の交換、各有限階の一様有界性を証明する。
`TestOn U` は台が開集合 \(U\) に含まれる試験関数である。

`LocallyConvex.topology` は、各コンパクト台の段階で連続な全ての seminorm の平行移動された開球から生成する試験関数の局所凸位相である。
`SeminormCharacterization.equivalence` は段階ごとの連続性と有限階評価の同値を証明する。
`Geometry` は原点中心の seminorm 球の balanced 性と凸性を証明し、`finestForContinuousSeminorms` は段階ごとに連続な任意の seminorm 族による位相との普遍的な比較を与える。
`LocallyConvex.ContinuousDual` と `Distribution` の変換は相互に逆である。

補助の `TestTopology.topology` は、各コンパクト集合に台を固定した \(C^\infty\) 空間からの包含に関する終位相である。
各段階では有限階までの全偏導関数の一様近傍を使う。
終位相の開集合の公理を証明し、連続性と各段階の \(\varepsilon\)–\(\delta\) 条件を比較する。

`Distribution` は線形汎関数と各コンパクト集合上の有限階評価を持つ。
`Bound value K m C` は、\(K\) に台を持つ試験関数の \(m\) 階以下の全偏導関数が \(b\) 以下なら \(|T\phi|\le Cb\) となる条件である。
`JetBounds.existsBound` が必要な有限上界の存在を保証する。
`TestTopology.Linear.dualCharacterization` はこの評価条件と実際の位相的連続性の同値を証明する。
`ContinuousDual` と `Distribution` の相互に逆な変換も公開する。

## 局所可積分関数

`Regular.LocallyIntegrable f` は可測性と全コンパクト集合への制限の可積分性を表す。
`Regular.For[f].pair test` は実際の Lebesgue 積分 \(\int f\phi\) である。
積の可積分性、線形性と零階の局所評価から正則分布を構成する。

`Regular.Space` は局所可積分関数の a.e. 同値類であり、`embed` はその分布への単射である。
単射性は、まず大域 L1 関数の試験関数による分離を畳み込みと L1 近似単位から証明し、コンパクト cutoff と可算な箱の exhaustion により局所の場合へ移す。

## 微分と収束

`Dual.partial T i` は \((\partial_iT)(\phi)=-T(\partial_i\phi)\) である。
有限階評価を一階ずらして分布であることを証明する。
`Dual.derivative directions T` は反復微分、`JetFormula[T].theorem` は任意階の符号付き試験関数公式である。
加法・スカラー倍との交換と混合偏微分の交換も公開する。

`Dual.Converges` は全試験関数に対する実数値の収束である。
`derivativesConverge` は任意階の分布微分とこの収束の交換を示し、`convergesUnique` は極限の一意性を示す。
`Examples.dirac` と `diracDerivative` は点評価分布とその微分の具体例である。

## 既存 Sobolev 空間との比較

`Regular.Sobolev` は既存の `functional_analysis.Sobolev[n].On[Open.whole]` と比較する。
実際の Lebesgue 測度を whole の部分型へ輸送し、積分と a.e. 同値を比較する。
既存の全偏導関数族付き `Test` と標準の `SmoothCompact` の相互変換を構成し、偏導関数の一意性から両方の試験関数の値を一致させる。

`DistributionComparison[u,g,d].equivalence` は旧定義の弱微分と \(\partial^d T_u=T_g\) の同値である。
`Finite[p].equivalence` は有限次数の全弱微分族の定義を比較し、`Space[k].toExisting/fromExisting` は既存の \(W^{k,p}\) 商との相互に逆な写像である。
ここでは \(1\le p<\infty\)、任意の非負整数次数と Euclid 空間全体を扱う。
`Regular.SmoothFunction[f].derivative` は A04 の部分積分から古典的偏微分と分布微分の一致を証明する。

## 台

`SupportTheory.support T` は、全ての局所試験関数を零へ送る開集合の和の補集合である。
`regularVanishes` は A04 の有限分解から、この和全体に台を持つ試験関数も零へ送られることを示す。
台は閉じており、閉集合への包含とその補集合上での消滅は同値になる。
空の台と零分布の同値、任意階の微分の台の包含、Dirac 分布の台が一点になることも証明する。

## 畳み込み

`Convolution.function T rho x` は \(T_y(\rho(x-y))\) である。
核 `rho` は任意の滑らかなコンパクト台関数で、分布 \(T\) に大域的な増大条件を課さない。
反射平行移動の共通コンパクト台と全階の偏微分公式を構成する。
平均値定理から差商誤差の有限階一様評価を導き、分布の局所評価を適用することで実際の偏微分を証明する。
`Convolution.smooth` が全階の滑らかさ、`Differentiation.partial` が偏微分表示、`DerivativeFormula.iterated` が分布の微分と核の微分の一致である。
`Convolution.Regular.integral` は局所可積分関数に対する実際の畳み込み積分、`LpComparison.agreement` は既存 Lp 畳み込みとの一致を示す。
`Examples.Smoothing` は Dirac 分布とその導関数による具体的な畳み込みを計算する。

## 開集合と微分同相

`On[U].LocallyConvex` は同じ seminorm 構成と連続双対の比較を開集合へ移す。
`On[U]` は台が \(U\) に含まれる試験関数とその連続双対を扱う。
局所評価のコンパクト集合は \(K\subset U\) を満たす。
`restrict` は大域分布の制限、`partialDistribution` は局所分布微分であり、`restrictDerivative` が制限と微分の交換を示す。
`On.SmoothRegular[f,smooth]` は局所滑らかな関数と試験関数の積を零延長し、実際の積分による正則分布を構成する。

`Pullback[U,V,e].apply` は微分同相 \(e:U\to V\) に沿う分布の引き戻しである。
試験関数には逆写像の絶対 Jacobian を掛ける。
\[
(e^*T)(\phi)=T\bigl(|\det D(e^{-1})|\,\phi\circ e^{-1}\bigr).
\]
`test` はこの密度変換を滑らかなコンパクト台関数として構成する。
高階の連鎖律とコンパクト集合上の係数評価から有限階の連続性評価を証明する。
`Composition.distributions`、`InverseLaw.source/target`、`PullbackIdentity.distribution` は合成、逆写像、恒等写像の法則である。
`SmoothRegular.distribution` は A04 の実際の積分変数変換と逆 Jacobian の相殺から \(e^*T_f=T_{f\circ e}\) を示す。
`Examples.Pullback.diracValue` は点分布に現れる密度係数を計算する。

## 検査

通常のキャッシュ付き checker で依存閉包、関連パッケージと登録済み workspace 全体を検査する。

```sh
cargo build -p cli --release --locked
target/release/cli libs/analysis/distributions --module distributions --memory-mib 8192
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288
```
