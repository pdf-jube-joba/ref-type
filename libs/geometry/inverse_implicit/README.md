# 逆関数・陰関数と正則値の局所形

Dedekind 実数上の滑らかな有限次元写像を扱う。
`calculus.Maps` の開集合間の写像から実際の局所逆写像を構成し、`manifolds` の多様体と微分に接続する。
零次元、空の正則ファイバーも含む。

| module | 公開する構成と定理 |
| --- | --- |
| `Euclidean[n].InverseFunction[U, f, a]` | 基点の微分の行列式が非零なら `localExistence` が `LocalInverse[U, f, a]` の存在を証明する |
| `Euclidean.LocalInverse` | 元の定義域に含まれる開近傍、像の開近傍、基点の所属、滑らかな両側逆と元の写像との一致 |
| `Product[n, m].Implicit[U, f, a]` | 未知変数方向の微分の行列式の非零性から、パラメータと方程式の値の積近傍上の解を構成する |
| `Product.Implicit.Solution` | 解写像、グラフ写像、方程式、局所一意性、近傍と積近傍の微分同相 |
| `Rank[n, m, r]` | 像への単射と像への全射による線形写像の階数の証明付きの分解 `Witness`、その存在を表す `HasRank` |
| `ConstantRank[k, r, l].On[U, f, a]` | 各点で階数 \(r\) の写像 \(\mathbb R^{k+r}\to\mathbb R^{l+r}\) に対する `localExistence` と `NormalForm` |
| `Product.Submersion[U, f, a]` | 微分の全射性から、元の写像を右の座標射影にする `LocalForm` を構成する |
| `Product.LocalFiber[U, f, a, local]` | 定値に固定したファイバーの滑らかなパラメータ表示とその両側の座標則 |
| `Product.LocalFiber.Tangent` | 座標の微分と逆微分による、パラメータ空間と微分の核との符号化・復号化 |
| `Product[n, m].RegularValue[M, T].Of[f, y]` | \(\dim M=n+m\)、\(\dim T=m\) の正則値ファイバー |
| `RegularValue.Of.manifold` / `Smooth.embedding` | 部分空間位相と飽和アトラスを持つ滑らかな多様体、および元の多様体への埋め込み |
| `RegularValue.Of.Smooth.At[x].identificationExists` | 包含の微分を順写像とする、ファイバーの接空間から元の微分の核への線形同型の存在 |

## 逆関数の構成

ヤコビアンの非零行列式の開集合へ制限し、基点の線形逆写像を後合成して基点の微分を恒等写像にする。
`Flat` は連続な偏導関数と平均値評価から、基点で微分が零の残差の局所縮小評価を導く。
`NearIdentity` は座標を閉球へ切り詰めた残差から、全ユークリッド空間上の縮小写像を作る。
既存の完備性と縮小写像定理により各像点の逆像を選び、評価から逆像が切り詰めの内部に入ることを示す。
これによって逆像の存在、局所一意性と距離評価を得る。

`InverseDifferential` は元の写像の剰余項、線形逆写像と逆写像の距離評価から逆写像の全微分を証明する。
`InverseRegularity` は逆行列族の滑らかさと連鎖律を用い、任意の滑らかなスカラー関数と逆写像との合成について微分の次数で帰納する。
これが構成した逆写像の滑らかさを与える。

## 陰関数と一定階数

座標を \((p,q)\) に分け、\((p,q)\mapsto(p,F(p,q))\) を作る。
`Triangular` は \(D_qF\) の逆からこの写像の微分の両側逆を明示的に組み立てる。
逆関数定理を適用し、像の積近傍へ制限した逆写像の右成分を解として使う。
`graphInside` と `coordinates` により、解のグラフが一意性を述べる近傍に入ることも公開する。

`Rank.Witness` は \(L=AB\) という純粋に線形な分解で、\(A:\mathbb R^r\to\mathbb R^m\) は単射、\(B:\mathbb R^n\to\mathbb R^r\) は全射である。
定階数定理では基点の \(A\) の左逆を用いて正則な成分を選び、全射の局所座標を構成する。
各点の階数分解と正方行列の片側逆から、残りの成分のパラメータ方向の微分が零であることを導く。
平均値評価から残りの成分はパラメータに依存しない。
最後に標的側の滑らかな shear を構成する。
`NormalForm.formula` は、構成した両側の微分同相について、元の写像が \((p,z)\mapsto(0,z)\) になることを述べる。

一般の全射線形写像の分解には、転置の単射性、Gram–Schmidt、核の直交射影の trace とその正規直交枠を使う。
座標の特定の小行列を全射性の代わりに入力する必要はない。

## 正則値ファイバー

`Regular` はファイバーの各点で、多様体の実際の微分が全射であることを表す。
接空間のチャート同型を用いて座標表示の微分の全射性を導き、`Submersion` の局所形を適用する。
標的の座標を正則値の座標に固定し、ファイバーのチャートを作る。
元のアトラスの遷移写像、局所微分同相、座標の固定と射影の合成によって遷移写像の滑らかさを証明する。
Hausdorff 性と第二可算性は部分空間位相から引き継ぐ。

包含は滑らかな埋め込みである。
接空間の核との同型では、包含の微分そのものを順写像に使う。
逆写像は、周囲の接ベクトルを局所座標へ移し、局所微分同相の微分を作用させ、パラメータ成分を取り出してファイバーの接空間へ戻す線形写像である。
核上の逆の法則と、包含の微分の単射性を証明する。

## 利用例と検査

[Examples.ref](src/Examples.ref) は非線形な shear \((u,z)\mapsto(u-z^2,z)\) に逆関数定理を適用する。
`Examples.Implicit` は \(F(p,q)=q-p^2\) にパラメータ付き陰関数定理を適用する。
`rankNormalForm` は階数一の非線形写像 \((u,z)\mapsto(u-z^2,0)\) に両側の局所座標を構成する。
`Examples.Manifold` は \(u-z^2=0\) の正則値部分多様体、包含の埋め込み、接空間と微分の核の線形同型を具体化する。
`Examples.ZeroDimension` は零次元の逆関数定理を検査する。

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --release --locked
target/release/cli libs/geometry/inverse_implicit --module inverse_implicit --full-check-local --memory-mib 8192 --cache-stats
python3 scripts/check_all.py --initial-memory-mib 8192 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512
```

最終ソースでの検査条件と結果は[検査記録](../../../benchmarks/records/inverse-implicit/README.md)にまとめる。
