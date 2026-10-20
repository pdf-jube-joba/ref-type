# 特異ホモロジー・コホモロジー

実装・検査完了（2026-10-20）。

有限 CW 空間の群・積・誘導写像を、特異理論との比較証明を伴って計算する。
本計画を一つの実装単位とする。

## 配置

- `algebraic_topology`：単体、道成分、円板・球面、有限 CW 構造。
- `metric_spaces`：Lebesgue 数、一様連続性、細分の距離評価。
- `topological_constructions`：積・商・貼り合わせ。
- `singular_cohomology`：鎖・余鎖・相対理論、ホモトピー。
- `singular_subdivision`：重心細分、小鎖、開被覆と部分空間の比較。
- `singular_excision`・`singular_products`・`singular_eilenberg_zilber`・`singular_symmetry`：切除、積、Eilenberg–Zilber 比較と交換ホモトピー。
- `singular_cech`・`singular_simplicial`・`singular_cellular`・`singular_cellular_algebra`：有限モデルとの比較。
- `singular_finite_algebra`・`singular_tensor_dual`・`singular_tensor_bridge`：有限模型の普遍係数・Künneth と係数の比較。
- `cohomology_models`・`sphere_maps`・`cohomology_examples`：計算と利用例。
- `singular_low_degree`：道を用いた鎖の正規化と積空間の一次コホモロジー。

分割後の全パッケージと公開 API の入口は [ライブラリ一覧](../../libs/README.md) にある。

加群・複体は `module_theory`・`chain_complexes`、有限モデルの普遍係数・Künneth は [ホモロジー代数](homological-algebra.md) を使う。
新規 package は約5,000行を目安に分割し、直接 import する依存と workspace member を登録する。

## 1. 単体と位相的な前提

`algebraic_topology.Simplex` に全頂点、アフィン写像、面の連続性、退化写像と恒等式、境界、重心を加える。
面の添字は \(0,\ldots,n\)、符号は \((-1)^i\)。
単体の閉性・コンパクト性、Lebesgue 数、一様連続性、重心細分の直径評価を示す。

## 2. 鎖・余鎖・相対理論

連続写像 \(\sigma:\Delta^n\to X\) 上の自由整数加群を \(C_n(X;\mathbb Z)\) とし、

\[
\partial_n[\sigma]=\sum_{i=0}^n(-1)^i[\sigma\circ\delta_i],
\qquad C^n(X;A)=\operatorname{Hom}_{\mathbb Z}(C_n(X;\mathbb Z),A),
\qquad\delta\varphi=\varphi\circ\partial_{n+1}
\]

で定める。
零次から負次数への境界は零。
面の恒等式から二乗零を、後合成から関手性を示し、係数群についての共変性と可換環係数の加群構造を公開する。
余鎖は任意の値の割り当てなので自由加群の Hom の積表示を使う。

相対鎖は \(C_*(X)/C_*(A)\)、相対余鎖はその Hom とし、\(A\) 上で零の余鎖との同型を示す。
生成元の補集合による次数ごとの分裂から、対の長完全列と自然性を得る。
増大複体で被約理論を定義し、\(\widetilde H_{-1}(\varnothing;\mathbb Z)=\mathbb Z\)、非空空間では零とする。

## 3. ホモトピーと零次

prism 分割から \(\partial P+P\partial=g_*-f_*\) を示し、相対理論を含むホモトピー不変性と可縮空間の計算を得る。
道成分の商を構成し、\(H_0\) はその上の自由可換群、\(H^0(X;A)\) は道成分から \(A\) への全関数の群と同型にする。

## 4. 細分・切除・Mayer–Vietoris

重心細分 \(S\simeq\mathrm{id}\) を構成する。
開被覆ごとの小鎖複体の包含を、面との整合性を保つ細分の選択により鎖ホモトピー同値にする。
Hom に渡して任意係数の余鎖も比較する。

\(\overline Z\subseteq\operatorname{int}_X A\) の切除と、開被覆 \(X=U\cup V\) に対する

\[
0\to C_*(U\cap V)\xrightarrow{(i_*,-j_*)}
C_*(U)\oplus C_*(V)\xrightarrow{a+b}C_*^{\{U,V\}}(X)\to0
\]

から両理論の長完全列を得る。
良い対の相対群と商の被約群を比較し、近傍変形収縮または CW 対の適用条件を明示する。

## 5. 球面と有限モデル

円板・境界球面を既存の `Euclidean.Dimension` に接続する。
\(S^0\) と二点空間の同相、二つの可縮な開集合の被覆と共通部分の変形収縮から、球面の群を帰納的に求める。
向き付き生成元、写像の次数・合成則、低次元セルの符号を定める。

有限順序付き単体複体の実現とアフィン特異単体の比較を構成し、細分・切除、星被覆の Čech 二重複体と担体ホモトピーで鎖ホモトピー同値を示す。
有限 CW 複体では

\[
C_n^{\mathrm{cell}}=H_n(X^n,X^{n-1};\mathbb Z)
\]

を向き付きセル上の自由可換群と同定し、三骨格の接続写像から境界を得る。
行列成分を付着写像の次数として証明し、任意係数の特異理論との自然な比較を公開する。

## 6. 積と係数

Alexander–Whitney・shuffle 写像による Eilenberg–Zilber の鎖ホモトピー同値と、対角による余鎖の積を構成する。

\[
(\alpha\smile\beta)(\sigma)=
\alpha(\sigma|[0,\ldots,p])\,\beta(\sigma|[p,\ldots,p+q]).
\]

余鎖上の結合・単位・自然性・Leibniz 則と交換ホモトピーから、コホモロジーの次数付き可換環を得る。
単体モデルの面公式との積の一致を示し、セルモデルには比較済みの単体モデルか証明付きセル対角を与える。

係数変更と Bockstein を構成し、証明済みの有限モデルへの比較後に普遍係数・Künneth を適用する。
積空間の公式には有限性と係数の条件を保持する。
照合先は Hatcher の [Chapter 2](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf) と [Chapter 3](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf)。

## 7. 計算と完了条件

生成元・関係・積・写像と元の特異理論との比較を、別 package の `cohomology_models`・`sphere_maps`・`cohomology_examples` から検査する。

| 空間 | 目標 |
| --- | --- |
| 空空間 | 非負次数の通常コホモロジーは零 |
| 非空可縮空間 | \(H^0\cong A\)、正次数は零 |
| \(S^0\) / \(S^n\)、\(n\ge1\) | \(A^2\) / 零次と \(n\) 次に \(A\)、その他は零 |
| 有限グラフ | 全域森から \(H^0\cong A^c\)、\(H^1\cong A^{e-v+c}\) |
| \(T^2\)、整数係数 | 次数1の \(a,b\) の外積代数、射影と因子交換の作用 |
| \(\mathbb{RP}^2\)、整数係数 | \(H^0=\mathbb Z\)、\(H^2=\mathbb Z/2\)、その他は零 |
| \(\mathbb{RP}^2\)、\(\mathbb F_2\) | \(\mathbb F_2[u]/(u^3)\)、\(\deg u=1\)、\(u^2\ne0\) |

実射影平面の球面商と円板貼り合わせモデルを同相にし、付着写像から境界の2倍を導く。
有限半単体的モデルの Alexander–Whitney 面公式と実際の特異三角形への制限で \(u^2\) を計算し、Bockstein が次数1の mod 2 生成元を次数2の整数生成元へ送ることを示す。
\(\mathbb F_2\) は整数商と二元表現を結ぶ。
球面の反転、円周の整数次数の写像、相対群の接続写像も検査し、モデル変更に対する一致を示す。
検査は [共有キャッシュと範囲選択](../../src/USAGE.md#検査とキャッシュ) を使う。

## 8. 要件と実装の対応

パッケージは `libs/topology/singular/` に、空間の構成は `libs/topology/homotopy/` に、利用例は `libs/topology/examples/` に配置する。
以下の API は定義だけでなく、比較写像・逆写像・等式や完全性の証明を含む。

| 要件 | 公開 API と説明 |
| --- | --- |
| 単体・退化・コンパクト性・距離評価 | [algebraic_topology](../../libs/topology/homotopy/README.md) の `Simplex`、`Degeneracy`、`Compactness`、`BarycentricSubdivision.At.Iterated.Decay`。Lebesgue 数と一様連続性は [metric_spaces](../../libs/topology/metric/README.md) の `MetricSpace.Compactness`・`Uniform`。 |
| 鎖・余鎖・相対・被約理論 | [singular_cohomology](../../libs/topology/singular/cohomology/README.md) の `Chains`、`Cochains.With.At.productIsomorphism`、`Relative.LongExact`、`Relative.With.Vanishing`、`Chains.Reduced.NegativeOne`。 |
| ホモトピー不変性と零次 | 同パッケージの `Homotopy`、`Relative.Maps.Over.Homotopy.On`、`Zero.Homology`、`Zero.With.Functions`、`Calculations.With.Contractible`。 |
| 細分と任意係数の小鎖比較 | [singular_subdivision](../../libs/topology/singular/subdivision/README.md) の `Subdivision`、`OpenCover.On`、`OpenCover.On.With.Homotopies`、`OpenCover.On.Subspace.Relative`。 |
| 切除・Mayer–Vietoris・良い対 | [singular_excision](../../libs/topology/singular/excision/README.md) の `Excision.Over`、`MayerVietoris.Over.On.Chains`、`GoodPair.On`。商との比較は近傍変形収縮のデータから構成する。 |
| 球面の群と向き | [cohomology_models](../../libs/topology/examples/cohomology/README.md) の `Geometry`、`ZeroSphere`、`SphereCover`、`Spheres.With`、`Spheres.Homology`、`Spheres.Orientation`。 |
| 反対点写像と整数次数の円周写像 | [sphere_maps](../../libs/topology/spheres/README.md) の `Antipodal.degree`、`ZeroAntipodal.With.Reduced`、`Circle.Powers.Actions.integer`。 |
| 単体的比較 | [singular_simplicial](../../libs/topology/singular/simplicial/README.md) の `Complex.On.Cech`、`Chains.HomotopyEquivalence`、`Chains.With.Comparison`。星の共通部分の収縮と担体ホモトピーからアフィン比較を証明する。 |
| セル鎖・付着次数・自然性 | [singular_cellular](../../libs/topology/singular/cellular/README.md) の `On.Cellular.Representatives.Selected`、`On.CellCollapse.Pair.Basis.Incidence`、`On.ZeroCollapse.Basis.Incidence`、`On.Naturality`。代表鎖の選択の存在も証明する。 |
| 積と交換ホモトピー | [singular_products](../../libs/topology/singular/products/README.md)、[singular_eilenberg_zilber](../../libs/topology/singular/eilenberg_zilber/README.md)、[singular_symmetry](../../libs/topology/singular/symmetry/README.md)。`Cochains.GradedCommutativity.law` と `ExternalCup` が類の交換符号と外積を与える。 |
| 有限模型での積の一致 | `singular_simplicial.Complex.On.Cup.Product.Compatibility`、`Cup.Finite.Product.Cohomology.onClasses`、`singular_cellular.On.Cellular.Representatives.Selected.Native.Diagonal.Cup`。 |
| 係数変更・普遍係数・Künneth | `singular_cohomology.Coefficients.Sequence.On` と [singular_finite_algebra](../../libs/topology/singular/finite_algebra/README.md) の `Integer.Finite.Compared`、`Integer.Product.Compared.Factors`、`Field.IntegralProduct.Factors`。有限性と係数の条件を型に保持する。 |
| 有限グラフ | [cohomology_examples](../../libs/topology/examples/finite_models/README.md) の `Graph.Counting.cycleRank`、`Graph.On.Geometry.Coefficients.Singular`。全域森・弦の座標を実現の特異コホモロジーへ移す。 |
| 整数係数のトーラス | 同パッケージの `Torus.Geometry.Comparison`、`Ring.Basis`、`Ring.UnitBasis`、`Ring.Primitive`、`Ring.Flip`。二つの射影類、その積による向き、因子交換の作用を計算する。 |
| 実射影平面の空間と群 | 同パッケージの `ProjectivePlane.Geometry.Attachment`、`Attachment.Base.attachingEquation`、`Attachment.Coefficients.Connecting`、`Cohomology`、`Integral`、`ModTwo`。球面商と貼り付け模型を比較し、境界の二倍写像から群を求める。 |
| 実射影平面の積と Bockstein | 同パッケージの `ProjectivePlane.Geometry.Restriction`、`ModTwo.Ring.square`、`Bockstein.law`。実際の特異三角形への制限と係数列の自然性により、有限計算の \(u^2=v\ne0\) と \(\beta(u)\) を元の空間へ移す。 |

全域森を与えたグラフでは、頂点数を \(v\)、辺数を \(e\)、成分数を \(c\)、弦数を \(k\) とすると、`Graph.Counting.euler` が \(e+c=v+k\)、`cycleRank` が \((e+c)-v=k\) を証明する。
トーラスと実射影平面の生成元は、それぞれ実際の特異コホモロジーの元として公開する。
実射影平面の二元体は `Two.Quotient.isomorphism` によって整数の二倍部分群による商と結ぶ。

## 9. 検査結果と再検査

`cohomology_examples` の依存閉包には、上記の特異理論の全パッケージ、球面の群と写像、単体的・セル的比較、および係数計算のホモロジー代数が含まれる。
次の検査は入口だけでなく、その依存閉包の全 module を対象にする。

```sh
cargo build -p cli --locked
target/debug/cli libs/topology/examples/finite_models --memory-mib 15360 --batch-seconds 900 --diagnostics compact
```

通常検査でも現在のソース・依存関係とキャッシュの一致を確認する。
個別の証明を編集するときは `--module` と `--module-only` を使い、依存閉包全体の検査で完了を確認する。

2026-10-20 に、依存閉包の41パッケージ・全5,000 module の検査を通過した。
上記の実装対応には、任意係数の自然性、付着次数とセルの向き、トーラスの積と因子交換、実射影平面の環構造と Bockstein の検査を含む。
