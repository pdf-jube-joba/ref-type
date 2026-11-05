# 多重積分の変数変換

Dedekind 実数上の Lebesgue 測度、滑らかなコンパクト台関数、開集合間の微分同相を扱う。
測度・積分は `euclidean_measure`、`functional_analysis.Measure`、`product_integration` の構成を使い、微分と局所逆写像は `calculus` と `inverse_implicit` を使う。

## 微分同相の変数変換

`Change.theorem n U V e f within` は任意の次元、開集合間の滑らかな微分同相 \(e:U\to V\)、\(V\) 内に台を持つ滑らかなコンパクト台関数 \(f\) について、
\[
\int_U |\det De_x|f(e(x))\,d\lambda_n(x)=\int_V f(y)\,d\lambda_n(y)
\]
を証明する。
零次元と空の開集合も含む。
`Euclidean[n].Diffeomorphism[U,V,e].Compact[f,within]` が左辺の密度の零延長、滑らかなコンパクト台、実際の Lebesgue 可積分代表を構成する。
主定理の被積分関数は `lp_spaces.Euclidean[n].SmoothCompact` であり、台の \(V\) への包含を明示する。

証明は座標交換と局所逆写像により一座標置換と第一座標固定写像へ分解する。
一座標の場合は閉直方体上の正向き・逆向きの一変数置換積分を Fubini で合わせ、第一座標固定の場合は切片の微分同相と行列式の小行列公式から次元帰納を使う。
最後にコンパクト台の有限分解で局所公式を貼り合わせる。
`Composition` と `Restriction` は実際の重み付き引き戻しの合成・制限の積分一致を証明する。
`NonlinearExample.integral` は既存の非線形 shear \((p,q)\mapsto(p-q^2,q)\) へ主定理を適用する。

## 線形写像と Jacobian

`Linear[n].Generated.measure` は任意の可逆線形写像 \(L\) と任意集合 \(S\) に対し、
\[
\lambda_n^*(L(S))=|\det L|\lambda_n^*(S)
\]
を外測度の拡張非負実数の下切断として証明する。
可測集合では Lebesgue 測度の変換則となる。
`measurable` は Lebesgue 可測性の保存を示す。
`Elementary.Elimination.factorization` が零次元を含む有限初等変換分解を構成し、対角変換、せん断、合成の測度公式へ接続する。
`OpenTransport` は同相写像の開集合上の定数倍則を外測度の外正則性で任意集合へ拡張し、Carathéodory 可測性を移す。
`Permutation.Smooth` は座標置換の滑らかな微分同相、絶対 Jacobian が一であること、コンパクト台の引き戻し積分の保存を提供する。

`Euclidean[n].Jacobian[U,V,f]` の `signed` は実際の全微分の行列式、`absolute` はその絶対値である。
`signedSmooth`、`Composition.signed/absolute`、`Inverse.nonzero/positive/cancellation` は滑らかさ、連鎖律、逆写像での非零性と相殺を証明する。
`Diffeomorphism.Regularity` は非零行列式の二乗の平方根から絶対 Jacobian の滑らかさを示す。

## 局所化とパラメータ

`Euclidean.Localization[U]` は、零延長の台が \(U\) に含まれ、コンパクトである滑らかな局所関数を大域の `SmoothCompact` と可積分代表へ移す。
`cutoff` はコンパクト集合の開近傍で一となる滑らかな cutoff を返す。
`Decomposition[family,f].exists` は \(\operatorname{supp}f\) の開被覆に従う有限個の滑らかなコンパクト台関数を構成する。
`Data.pointwise` が有限和と元の関数の一致、`Sum.theorem` が実際の積分と有限個の積分の和の一致である。
`BorelCompact` は同じ関数を Borel 測度上の可積分代表として構成し、完備 Lebesgue 測度上の積分と一致させる。

`Parameters.derivative` は積分可能な差商の支配と点ごとの微分から積分と微分を交換する。
`Parameters.Compact[function,partial].For[conditions].theorem` は、パラメータごとの滑らかなコンパクト台関数について、近傍で共通の有限測度領域と偏導関数の一様上界から支配関数を構成する。
`Parameters.Multivariable.At.theorem` は同じ結果を任意の有限次元パラメータの各偏微分へ移す。

## 部分積分と境界

`Euclidean.Compact.integralDerivative` は任意座標方向の滑らかなコンパクト台関数の偏導関数の積分が零であることを示す。
`Compact.IntegrationByParts[f,g,i].theorem` はコンパクト台を持つ \(f\) と任意の滑らかな \(g\) に対して
\[
\int (\partial_i f)g=-\int f\partial_i g
\]
を証明する。

`Interval[interval].Fundamental`、`IntegrationByParts`、`Substitution`、`ReverseSubstitution` は閉区間上の公式を提供する。
置換積分は順向きと逆向きの両方を扱い、`For.Absolute.theorem` が導関数の絶対値を含む Lebesgue 積分の等式である。
`RealLine.Monotone` は導関数の符号と平均値の定理から区間像・内点像を証明し、これらの条件を構成する。

`Boundary[n].Strip` は \(\mathbb R^n\times[a,b]\) の境界公式、`Rectangle` は底面を直方体へ制限した公式、`Strip.HalfSpace` は上側で消える場合の半空間公式を提供する。
`IntegrationByParts` は積の微分から境界付き部分積分を導く。
Fubini の例外零集合を扱い、境界差の可積分性も結論に含む。
`Bridge[n]` は積空間と \(\mathbb R^{n+1}\) の座標を結合し、Borel 集合上の測度比較と可積分代表の輸送を証明する。
その `Strip`、`Rectangle`、`IntegrationByParts` の各 `For.theorem` と `Strip.HalfSpace.theorem` が実際の Euclid 測度による境界公式であり、`Permuted` は任意座標への置換版である。
座標関数の Borel 可測性は明示する。

## 密度と最高次形式

`Euclidean.Density.pullback` は \(h\mapsto |\det Df|h\circ f\) であり、非負性、合成則、逆写像での復元を証明する。
`TopCoordinates[U]` は滑らかな係数と最高次形式 \(h\,dx_1\wedge\cdots\wedge dx_n\) の相互に逆な対応を与える。
`TopForm.coordinate` は実際の `euclidean_forms` の pullback の最高次係数が \((\det Df)h\circ f\) になることを示す。
密度は絶対行列式、向き付き最高次形式は符号付き行列式を使う。

`Examples[n].IdentityOn` は零次元を含む恒等写像の Jacobian と密度変換を検査する。

## 検査

通常 release checker で対象、ソースからの局所再検査、依存の回帰、リポジトリ全体を検査する。
最終ソース、命令、終了コード、対象数、キャッシュとメモリの記録は [A04 検査記録](../../../benchmarks/records/a04-change-of-variables/README.md) にまとめる。

```sh
cargo build -p cli --release --locked
target/release/cli libs/analysis/change_of_variables --module change_of_variables --full-check-local --memory-mib 8192
python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288
```
