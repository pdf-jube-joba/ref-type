# Stone–Weierstrass と Laurent 近似

コンパクト Hausdorff 空間上の実・複素関数の一様近似と、円周上の Laurent 近似を扱う。
行列の有限成分と、有限埋め込みで表示した複素束の自己準同型に適用する。
入口は `Approximation`、package 名は `uniform_approximation`。

## 実関数と複素関数

`On[X, space]` は実数値関数、`ComplexOn[X, space]` は複素数値関数を扱う。
`SubalgebraLaws` は連続性、すべての定数、和・負・積への閉性をまとめ、複素版では共役への閉性も含む。
`Separates` は異なる二点で値の異なる元の存在である。
`Error f g epsilon` は全点での厳密な誤差評価、`Approximates A f` は任意の正の誤差に対する部分代数の元の存在を表す。
複素誤差は既存の Euclid 絶対値 `complex.Complex.Absolute.abs` を使う。

| API | 内容 |
| --- | --- |
| `Polynomials` | 既存の実係数多項式環とその評価、帰納法、反復多項式 `absolutePolynomial` |
| `Absolute.unitBounded` | 全実数 \(\lvert x\rvert\leq1\) での絶対値の一様多項式近似 |
| `On.Dini.uniform` | 連続な非負誤差の単調減少と点ごとの近似から、有限部分被覆で一様化する |
| `On.Compact.RealAlgebra.StoneWeierstrass.approximation` | 点を分離する実部分代数による、任意の連続実関数の一様近似 |
| `ComplexOn.Algebra.Compact.StoneWeierstrass.approximation` | 共役に閉じ、点を分離する複素部分代数による一様近似 |
| `ComplexOn.Naturality` | 誤差・近似・定数・和・積・共役の引き戻しとの可換性 |

絶対値の近似は \(p_0=0\)、\(p_{n+1}=p_n+(x^2-p_n^2)/2\) を既存の多項式環で構成する。
\(0\leq p_n(x)\leq\lvert x\rvert\leq1\) と幾何級数による点ごとの収束を証明し、コンパクト性で一様化する。
部分代数の一様閉包について代数演算・極限・絶対値・最大最小への閉性を証明し、二点補間と二度の有限部分被覆から実版を得る。
複素版は共役による実部・虚部の抽出と実版を使い、二成分の誤差から複素絶対値の誤差を評価する。

## 円周と連続係数

`Circle` は既存の `sphere_maps.Circle` を使い、既存の球面との同相からコンパクト性と Hausdorff 性を得る。

| API | 内容 |
| --- | --- |
| `Circle.Scalar.Polynomial` / `value` | `algebra.LaurentPolynomial.Over` の複素数係数の元と円周上の評価 |
| `Circle.Scalar.Approximate.exists` | 任意の連続な円周上の複素関数の Laurent 近似 |
| `Circle.Scalar.Matrices[n, m].exists` | 零サイズを含む有限行列の、同じ誤差による Laurent 成分の同時近似 |
| `ComplexOn.FunctionRing` | 連続複素関数の可換環、共役、点での環準同型としての評価 |
| `Circle.Coefficients[X, space, baseCompact, baseHausdorff]` | 連続係数関数環上の既存の Laurent 環 `Polynomial` と \(X\times S^1\) 上の `value` |
| `Circle.Coefficients.Approximate.exists` / `Matrices.exists` | 積上の連続関数と有限行列の、連続係数を持つ Laurent 近似 |
| `Laurent.On.Reparameterization` | 底への写像と円周の単位関数を合成したときの評価・誤差の可換性 |

係数付き版の部分代数は、実際の Laurent 環の元の評価像である。
その連続性と共役閉性は Laurent 環の公開帰納法で証明し、底の異なる点は Urysohn 関数、円周の異なる点は変数で分離する。
円周単独版では一点上の係数関数を複素数係数に翻訳し、評価の一致を証明する。
`Circle.Scalar.Translation` がこの比較を公開し、`Subalgebra`・`algebraLaws`・`separation` は有限成分・束への適用にも使える。

## 有限成分、束、可逆性

`FiniteChoices` と `ComplexOn.FiniteComponents` は有限個の近似を共通の誤差で選び、`Matrices.On.density` は実際の行列族へまとめる。
`FiniteComplex` は既存の有限和とその列挙を再利用する。
`Matrices.actionError` は成分誤差 \(\leq\delta\) から、作用の各成分の誤差 \(\leq\delta\sum_j\lvert v_j\rvert\) を導く。
`compressedError` は左から行列を作用させたときの増幅係数も有限和で評価する。

`Bundles.Over[X, F, bundle].splittingExists` は B03 の有限埋め込みと像への比較同型から、実際の束写像 \(E,C\) と \(CE=1\) を構成する。
以下では `Split[n, include, project, retraction]` を `Split` と書き、\(P=EC\) とする。

| API | 内容 |
| --- | --- |
| `Split.MatrixMap.compressed` | 連続行列族 \(a\) から束写像 \(CaE\) を構成する |
| `Split.Approximate[h].matrix` / `regular` | 自己準同型 \(h\) を周囲の連続行列 \(EhC\) へ移す |
| `Split.Approximate.Density.uniformExists` | 部分代数の成分を持つ実際の近似行列と圧縮した束写像を構成し、\(\sum_j\lvert(Ev)_j\rvert\leq1\) 上で全成分の誤差 \(<\epsilon\) を証明する |
| `Split.ProjectionBound.exists` | コンパクト性による射影の全行に共通な正の上界 |
| `Split.Invertible.isomorphism` | 射影と可換な連続可逆行列族から、連続な逆束写像を持つ同型を構成する |
| `Split.Lift` | \(PaP+(1-P)\) の連続性、射影との可換性、元の圧縮との一致 |
| `Split.Lift.Invertible.isomorphism` / `forwardEquals` | 行列式の相対誤差条件から同型を構成し、その順写像が元の圧縮であることを示す |

`Matrices.invertibleOfDeterminantError` の条件は \(\lvert\det b-\det a\rvert<\lvert\det a\rvert\) である。
`Matrices.On.Margin.exists` はコンパクト底上の連続可逆行列族について \(0<\eta\leq\lvert\det a(x)\rvert\) を構成し、`invertibleError` は一様な行列式の誤差 \(<\eta\) から逆行列の存在を導く。
束への適用では `Lift.matrix` にこの条件を課し、L01 の逆行列と L03 の連続性を再利用する。

## 利用例と検証・再開

[Examples.Circle](src/Approximation/Examples/Circle.ref) は円周上の \(\lvert\operatorname{Re}z\rvert\) の近似、2行2列と零サイズの Laurent 行列を使う。
[Examples.Coefficients](src/Approximation/Examples/Coefficients.ref) は \(g(x)z^{-1}\) の実際の多項式と評価式を比較する。
[Examples.Bundle](src/Approximation/Examples/Bundle.ref) は円周上の自明線束の自己準同型を単位球上一様に近似する。
[Examples.IdentityMatrix](src/Approximation/Examples/IdentityMatrix.ref) は任意次元の恒等行列で可逆性の誤差条件を使う。

基点は K01 統合済み main `f6c3dcfb`、ブランチは `math/k04-uniform-approximation`、[draft PR #45](https://github.com/pdf-jube-joba/ref-type/pull/45)。
最後に成功した対象検査は `71ddcdd1` の `work/k04-examples`（終了0・共有キャッシュ保存完了）。
公開 API と利用例まで対象スコープで検証済みで、数学ソースへの未検証変更はない。
次は対象 package の全依存閉包と、共通化した B03 `CoordinateFamily` の利用先を含む workspace を固定 snapshot で検査する。

```sh
target/debug/cli libs --parse-only --save-source-snapshot work/k04-package.source.json
target/debug/cli libs/analysis/uniform_approximation --source-snapshot work/k04-package.source.json --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 1800 --report-json work/k04-package.report.json
target/debug/cli libs --source-snapshot work/k04-workspace.source.json --memory-mib 10240 --cache-budget-mib 12288 --time-limit-seconds 7200 --report-json work/k04-workspace.report.json
```

検査の正常終了とキャッシュ保存完了を確認してから、依存リンク・ロードマップの完了処理と PR の最終確認・統合へ進む。
