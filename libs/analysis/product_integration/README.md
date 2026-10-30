# 積測度と反復積分

`product_integration` は σ 有限測度の積、Tonelli・Fubini と畳み込みの評価を提供する。
測度と実積分には `functional_analysis.Measure`、Euclid 測度には [euclidean_measure](../euclidean_measure/README.md)、複素・有限次元の積分には [measure_convergence](../measure_convergence/README.md) を使う。

`Finiteness[A, mu].Exhaustion` は有限測度の可測集合による可算被覆を表す。
集合列を互いに素な増分へ分け、有限な制限測度の積を可算和にしたものが `Product[A, B, mu, nu, left, right].measure` である。
`ProductSigma.sigma` は可測長方形の生成する σ 代数で、両方向の切断は可測となる。
`Product.sigmaFinite` は構成した積測度自身の σ 有限性を示す。
`Product.Rectangle.formula` は一般の可測長方形について拡張非負値の二重級数による公式を、`FiniteRectangle.theorem` は両辺の測度が有限な場合の積の公式を示す。
`Symmetry.map` は左右交換が測度を保つことを表す。

```ref
\import product_integration.Integration[
  A := A, B := B, mu := mu, nu := nu, left := left, right := right] \as F;
\import product_integration.Product[
  A := A, B := B, mu := mu, nu := nu, left := left, right := right] \as P;
\import product_integration.ProductSigma[
  A := A, B := B, left := mu.sigma, right := nu.sigma] \as S;
\import functional_analysis.Measure[A := S.Point].Integral[mu := P.measure] \as I;

\definition example: \forall (f: I.Representatives) -> \exists F.AEFubini[f] := F.fubini;
```

`Integration.tonelli` は非負可測実関数について、積測度の下積分と切断の下積分の反復積分を同一視する。
内側の積分が無限となる点も扱い、外側の拡張非負値関数の積分は `ExtendedIntegral.lowerIntegral` で表す。
`Integration.fubini` は絶対可積分実関数に対して `AEFubini` の存在を証明する。
この構造は可測零集合、零集合の外で元の切断と一致する可積分代表、切断積分を値とする外側の可積分代表、積分交換の等式を含む。
`Complex.fubini` と `Vector[n].fubini` は同じ結論を実部・虚部と有限個の成分へ拡張し、共通の例外零集合を返す。
零次元のベクトルも含む。

`Euclidean[n].exhaustion` は Lebesgue 測度の有限な箱による被覆である。
`EuclideanProduct[m, n].join` は二つの座標列を連結し、`split` はその逆写像である。
`Volumes.theorem` は箱の体積との一致を、`Comparison.theorem` は連結写像で送った積測度と高次元 Lebesgue 測度が全 Borel 集合上で一致することを示す。
`Comparison.domination` は積測度で可測な任意の集合について、送った測度が Euclid の外測度以下であることを示す。
比較の等式の対象は Borel 集合であり、積の σ 代数を完備化したとする宣言は含めない。

`Convolution[A, mu, exhaustion].For[translations, f, g]` は測度を保つ移動の族と二つの実可積分関数を扱う。
`kernel(x, y)` は \(f(x-y)g(y)\) に対応し、`exists` はその共同可測性から切断の a.e. 可積分性、外側の可積分代表、
\[
\int f*g=(\int f)(\int g),\qquad \|f*g\|_1\leq\|f\|_1\|g\|_1
\]
を導く。
共同可測性は積の σ 代数に関する十分条件として明示する。
`Support.theorem` は \(f,g\) がそれぞれ \(S,T\) の外で零なら、畳み込みが共通の例外零集合と \(S+T\) の外で零となることを示す。
`Euclidean[n].translation` は \(x\mapsto x-a\) の測度保存写像を与え、`Euclidean[n].Convolution` が Euclid 空間の API となる。

補助 API として、生成 σ 代数の π–λ 定理、有限測度の一意性、測度保存写像による実積分の移送、測度の可算和と下積分の交換、上限と非負級数の交換を公開する。
`Examples[n]` には零関数の Fubini、零関数と任意の可積分関数の畳み込み、箱の比較の検査される利用例がある。

通常検査はリポジトリのルートで次を実行する。

```sh
target/release/cli libs/analysis/product_integration --module product_integration --diagnostics compact --no-progress --memory-mib 6144
cargo build -p cli --release --locked && python3 scripts/check_all.py
```
