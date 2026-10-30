# 滑らかな cutoff と従属分割

Dedekind 実数上で平坦な関数、Euclid 空間のコンパクト台付き cutoff、第二可算 Hausdorff 多様体の滑らかな従属分割を構成する。
利用例は [実直線](src/Examples/Line.ref) と [零次元のコンパクト多様体](src/Examples/Point.ref) にある。

## 解析的構成

`Exponential.Global.value` は実数全体で正値、\(E(0)=1\)、\(E'=E\) を満たす指数関数である。
既存の滑らかな常微分方程式の局所解を区間の倍増で延長し、商の微分と平均値の定理で延長の一致を示す。
加法則と \(t>0\) に対する \(t\le E(t)\) も証明する。
`Global.Smooth.family` は任意階の偏導関数が同じ指数関数になることを表す。

`Exponential.Flat.Polynomial.Smooth.value` は \(t>0\) では \(E(-1/t)\)、\(t\le0\) では零である。
導関数は \(P(1/t)E(-1/t)\) の形を保つ。
`Polynomial.rapid` は任意の多項式式 \(P\) と正の \(c\) に対して、正側の \(P(1/t)E(-c/t)\) を零延長した関数が零へ収束することを示す。
積のときは指数の係数を半分ずつに分けるため、全階微分について境界での収束を証明できる。
`Smooth.family` と `allDerivativesZero` が、全階の微分の仕様と非正領域での消滅を公開する。

`Exponential.Step.value` は \(t\le0\) で零、\(t\ge1\) で一となる滑らかな段差関数で、値は \([0,1]\) にある。
`Plateau.value` は \([-1,1]\) で一、\(( -2,2 )\) の外で零となる。

## Euclid 空間

| API | 内容 |
| --- | --- |
| `Euclidean[n].LocalBump[a, q]` | 正の \(q\) に対し、最大値ノルムの開球 \(B(a,q)\) で一、台が閉球 \(\overline B(a,2q)\) に含まれる滑らかな関数 |
| `LocalBump.Support` | 台の包含、閉球と台のコンパクト性 |
| `CompactCutoff[K, U].existsCutoff` | コンパクトな \(K\subset U\) と開集合 \(U\) に対し、\(K\) の開近傍で一、コンパクトな台が \(U\) に含まれる cutoff の存在 |
| `Jets[f].allOrdersZero` | 任意階の微分族について、台の外ではすべての偏導関数が零になること |
| `ZeroExtension[U, f].smooth` | 零延長の台が \(U\) に含まれる場合の滑らかさ |
| `ZeroExtension.Closed[F].smooth` | 閉集合 \(F\subset U\) の外で零という条件からの零延長 |
| `LocallyFinite[f].Sum[local].smooth` | 近傍ごとに有限個の項だけが残る可算和の滑らかさ |

`CompactCutoff.Data` は関数、\(K\) を含む開近傍、その近傍上で一になる証明、台の包含とコンパクト性、値域の両端の評価を持つ。
滑らかさは既存の `calculus.Open.Smooth` の全階偏微分による仕様である。
零次元も含み、有限座標の積は座標数零では一になる。

## 多様体

入口は `Manifold[n].On[M]` である。
`IsSmooth f` は最大アトラスの各チャートでの実際の座標表示が滑らかであることを表す。
`Continuity.continuous` と `Locality.smooth` が連続性と局所判定を与える。

`Partitions[family].existsPartition` は任意の開被覆に対して `Scalars.Using.SmoothPartition` を返す。
各項の滑らかさ、非負性、一以下の評価、コンパクトな台、被覆への台の従属性、台の局所有限性、総和一を含む。
`Refinement[family, partition]` の `region` は各項の正値集合で、`open`、`covers`、`within`、`locallyFinite` が局所有限な開細分を与える。
`target` は非空の各細分集合に対して元の被覆の要素への包含を与える。
空集合を添字に含めることを許している。

構成は、各点で一になるコンパクト台付きチャート bump を選び、第二可算性から可算部分被覆を取る。
選んだ bump を \(b_i\) として、
\[
r_0=1,\qquad r_{i+1}=r_i(1-b_i),\qquad \phi_i=b_i r_i
\]
と置く。
各点のある開近傍で一つの \(b_i\) が一になるので、それ以降の \(\phi_j\) の台はその近傍と交わらない。
有限部分和と余りの和が一になる恒等式から総和一を導く。

`existsFinitePartition` はコンパクトな場合に有限版を返す。
`FinitePartition.size` と、その数より小さい添字の関数・従属先・総和の仕様を公開する。
コンパクト性から可算被覆の有限な初期部分を取り出す証明は `Scalars.Using.Sequence.FiniteCover` にある。

`OnOpen[U, open].IsSmooth` は開集合上のスカラー関数を扱う。
その `ZeroExtension.smooth` と `ZeroExtension.Closed.smooth` が、台の条件付き零延長を与える。
`LocallyFinite.Sum.smooth` は多様体上の局所有限和を、近傍で有限部分和と一致することから構成する。

## 切断の零延長

`Sections[F, zero]` はファイバーの集合族と零ベクトルを取り、有限次元の局所ファイバー座標 `Frame` を使う。
フレームは開領域、座標と逆座標、その領域での両側逆、および零を保つ性質を持つ。
`Over[atlas].IsSmooth` は各フレームの領域上で全座標成分が滑らかな切断を表す。
これは零を保つ局所座標を備えた束に適用でき、線形な局所自明化はこの条件を満たす。

`Over.Open[U, open].ZeroExtension` は依存する各ファイバー内で零延長を構成し、`inside` と `outside` で値を計算する。
その台は零ベクトルでない点の閉包である。
`smooth` は台が \(U\) に含まれる場合の滑らかさを、`Closed.smooth` は閉集合 \(F\subset U\) の外で零の場合の滑らかさを示す。
証明は各局所ファイバー座標の零保存性と `GluingOn.smooth` による局所的な貼り合わせからなる。

## 検査

最終ソースでの対象・関連検査と通常全体検査の結果は [検査記録](../../../benchmarks/records/smooth-partitions/README.md) にある。

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --release --locked
target/release/cli libs/geometry/smooth_partitions --module smooth_partitions --memory-mib 10240
python3 scripts/check_all.py --initial-memory-mib 10240 --memory-mib 10240
```
