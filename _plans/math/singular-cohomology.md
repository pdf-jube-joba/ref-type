# 特異ホモロジー・コホモロジー

有限 CW 空間の群・積・誘導写像を、特異理論との比較証明を伴って計算する。
本計画を一つの実装単位とする。

## 配置

- `algebraic_topology`：単体、道成分、有限単体複体と実現、有限 CW 構造。
- `metric_spaces`：Lebesgue 数、一様連続性、細分の距離評価。
- `topological_constructions`：積・商・貼り合わせ。
- 新規 `libs/topology/singular_cohomology`：鎖・余鎖・相対理論、ホモトピー、細分、切除、積、有限モデルとの比較。
- 新規 `libs/topology/cohomology_models`：計算と利用例。

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

有限順序付き単体複体の実現とアフィン特異単体の比較を構成し、細分・切除・骨格帰納法で鎖ホモトピー同値を示す。
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

生成元・関係・積・写像と元の特異理論との比較を、別 package の `cohomology_models` から検査する。

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
有限三角形分割の Alexander–Whitney 公式で \(u^2\) を計算し、Bockstein が次数1の mod 2 生成元を次数2の整数生成元へ送ることを示す。
\(\mathbb F_2\) は整数商と二元表現を結ぶ。
球面の反転、円周の整数次数の写像、相対群の接続写像も検査し、モデル変更に対する一致を示す。
検査は [共有キャッシュと範囲選択](../../src/USAGE.md#検査とキャッシュ) を使う。
