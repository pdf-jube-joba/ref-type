# 特異コホモロジーと具体的な計算

## 到達点

任意の位相空間の整数特異鎖複体、可換群係数の特異コホモロジー、相対群、誘導写像を構成する。
ホモトピー不変性、切除、Mayer–Vietoris、有限単体・セル複体との比較、カップ積を証明し、有限モデルから特異コホモロジーの群・積・写像を計算する。
到達例は一点・空間の空集合・球面・有限グラフ・トーラス・実射影平面とする。
実射影平面では整数係数のねじれと \(\mathbb F_2\) 係数のカップ平方まで求める。

代数的な核・像・商は `module_theory`、一般複体と長完全列は `chain_complexes`、Hom 複体は `resolutions`、Ext・Tor は `derived_functors`、有限行列計算は `integer_matrices`・`finitely_generated_modules`・`homological_algebra` の既存 API を使う。
[ホモロジー代数計画](homological-algebra.md) の普遍係数短完全列全体の自然性・整数 Künneth・体係数の標準外積同型は、第6・7節で必要になる。
有限モデルの係数付き群の計算には、`homological_algebra.Finite.Bounded` の普遍係数短完全列と分裂を使う。
第1〜5節は既存の基盤から進められる。
本計画全体を一つの実装単位とし、以下の節は中間検査点とする。
De Rham 同型、Poincaré 双対性、一般の無限 CW 複体、局所係数、スペクトル系列による計算は、今回の構成から進む後続の単位とする。

## 追加する構成の配置

既存の公開 API は [ライブラリ一覧](../../libs/README.md) と各 README を参照する。
空間の幾何的な構成と、鎖複体による不変量を次のように分ける。

| 配置・パッケージ | 追加する module 群と役割 |
| --- | --- |
| [topology/metric_spaces](../../libs/topology/metric_spaces/README.md)・`metric_spaces` | Lebesgue 数、一様連続性、細分の距離評価 |
| [topology/topological_constructions](../../libs/topology/topological_constructions/README.md)・`topological_constructions` | 幾何的実現に必要な積・商・貼り合わせの補題 |
| [topology/algebraic_topology](../../libs/topology/algebraic_topology/README.md)・`algebraic_topology` | `Simplex` の連続写像と合成則、`PathComponent`、`SimplicialComplex`、`Realization`、具体的な空間と有限 CW 構造 |
| `libs/topology/singular_cohomology`・`singular_cohomology`（新設） | `Chains`、`Cochains`、`Relative`、`Homotopy`、`Subdivision`、`Excision`、`MayerVietoris`、`Simplicial`、`Cellular`、`Product`、`Cup`、`Coefficients`、`Calculations` |
| `algebra/homological/derived_functors`・`derived_functors`、`algebra/homological/computations`・`homological_algebra` | 普遍係数・Künneth と、位相的に比較した有限モデルとの接続 |

`singular_cohomology` は `std`、`module_theory`、`commutative_algebra`、`chain_complexes`、`resolutions` と幾何側の `real`、`topology`、`metric_spaces`、`topological_constructions`、`topological_algebra`、`algebraic_topology` を直接 import する範囲に応じて依存に持つ。
第6・7節で導来関手と有限計算を利用する際は `derived_functors`・`homological_algebra` を加える。
新規パッケージは `std` 以外の約5,000行という目安に従い、細分・比較・積・計算を共有基盤から応用への依存で分け、`singular_cohomology` から公開する。
幾何的な実現と空間の構成は `algebraic_topology`、そのコホモロジーの計算と比較定理は `singular_cohomology` が担当する。
`algebraic_topology` から `singular_cohomology` への依存は生じない構成とする。
実数係数には `real/basic` の `real` を使い、後続の De Rham 同型は `geometry/differential_forms` の `differential_forms` に接続する。
多様体と局所形式は、それぞれ `geometry/manifolds` の `manifolds` と `geometry/euclidean_forms` の `euclidean_forms` を使う。

## 1. 標準単体と位相的な前提

`algebraic_topology.Simplex.Carrier`・`At.topology`・`face` を使い、全頂点、アフィン写像、面写像の連続性、退化写像と合成恒等式、境界、重心を追加する。
面写像の添字は \(0,\ldots,n\)、境界の符号は \((-1)^i\) とする。
別パッケージでの次数付きの族と面の公式の確認は、[Simplices.ref](../../libs/topology/cell_spaces/src/Simplices.ref) に追加する。

単位区間の有限積のコンパクト性、単体の閉性、コンパクト距離空間の Lebesgue 数と連続写像の一様連続性を証明する。
重心細分の直径評価と、有限鎖の各特異単体を十分細分すれば被覆の一つに入ることを示す基盤にする。

## 2. 特異鎖・余鎖・相対群

位相空間 \(X\) の特異 \(n\)-単体を連続写像 \(\Delta^n\to X\) とし、その集合上の自由整数加群を \(C_n(X;\mathbb Z)\) とする。
正次数の境界を

\[
\partial_n[\sigma]=\sum_{i=0}^{n}(-1)^i[\sigma\circ\delta_i]
\]

で定め、零次から負次数への境界は零写像にする。
面写像の合成恒等式と符号の打ち消しから \(\partial^2=0\) を証明する。
連続写像との後合成を生成元から延長して鎖写像を作り、関手性を証明する。

可換群 \(A\) に対して

\[
C^n(X;A)=\operatorname{Hom}_{\mathbb Z}(C_n(X;\mathbb Z),A),
\qquad \delta\varphi=\varphi\circ\partial_{n+1}
\]

と定め、`chain_complexes` の `Cohomology` で \(H^n(X;A)\) を構成する。
余鎖はすべての特異単体への任意の値の割り当てであり、自由加群の普遍性から得る積加群の表示を利用する。
空間についての反変性と係数群についての共変性を証明する。
係数が可換環の場合は、その環上の加群構造まで公開する。

部分空間 \(A\subseteq X\) には生成元の包含から \(C_*(A)\subseteq C_*(X)\) を作り、相対鎖複体を商として構成する。
相対余鎖はこの商から係数群への Hom とし、\(A\) 上で零になる余鎖との同型を示す。
生成元の補集合による次数ごとの分裂から、対の鎖・余鎖の短完全列と長完全列、写像対についての自然性を得る。

増大写像 \(C_0(X;\mathbb Z)\to\mathbb Z\) とその増大複体で被約理論を定義する。
負次数を含む規約を固定して、空空間では \(\widetilde H_{-1}(\varnothing;\mathbb Z)=\mathbb Z\)、非空空間ではこの群が零になることを検査する。

## 3. ホモトピー不変性と零次

\(\Delta^n\times[0,1]\) の prism 分割から、ホモトピーに対応する次数を一つ上げる鎖作用素を構成する。
\(\partial P+P\partial=g_*-f_*\) を証明し、鎖ホモトピーからホモロジー・コホモロジーのホモトピー不変性を得る。
相対ホモトピーと対の長完全列にも接続する。
一点への収縮を使って可縮空間の群を計算する。

道による同値関係とその商 \(\pi_0^{\mathrm{path}}(X)\) を構成する。
\(H_0(X;\mathbb Z)\) はこの集合上の自由可換群、\(H^0(X;A)\) はこの集合から \(A\) への全関数の群と同型になることを証明する。
後者は各道成分上で一定という条件であり、一般空間でもこの定義をそのまま適用する。

## 4. 細分・切除・Mayer–Vietoris

重心細分の鎖写像 \(S\) と \(S\simeq\mathrm{id}\) の鎖ホモトピーを構成する。
開被覆 \(\mathcal U\) に対して、一つの被覆要素に像が含まれる特異単体から生成される小鎖複体 \(C_*^{\mathcal U}(X)\) を作る。
有限鎖ごとの十分な細分と、鎖の面との整合性を保つ帰納的な選択から、小鎖複体の包含が鎖ホモトピー同値であることを証明する。
この同値を Hom に渡して、任意の係数群で余鎖側も比較できるようにする。

\(\overline Z\subseteq\operatorname{int}_X A\) の条件下で、\((X\setminus Z,A\setminus Z)\to(X,A)\) が相対群の同型を誘導する切除定理を証明する。
\(X=U\cup V\) が開被覆なら

\[
0\to C_*(U\cap V)\xrightarrow{(i_*,-j_*)}
C_*(U)\oplus C_*(V)\xrightarrow{a+b}
C_*^{\{U,V\}}(X)\to0
\]

を構成し、鎖と余鎖の Mayer–Vietoris 長完全列を導く。
包含と接続写像の符号・自然性を固定する。
良い対では相対群と商空間の被約群の同型を証明し、適用条件を閉部分空間と近傍変形収縮、または証明済みの CW 対の条件として記録する。

## 5. 球面と有限モデルへの比較

`algebraic_topology.Euclidean.Dimension` の \((n+1)\)-次元円板と境界球面を使い、\(S^0\) と二点空間の同相を証明する。
二つの可縮な開集合による被覆と、共通部分の \(S^{n-1}\) への変形収縮を与え、Mayer–Vietoris で球面の被約群を帰納的に計算する。
円板と境界の相対群、球面の向きに対応する整数生成元、写像の次数と合成則を定義する。
零次元のセルと一次元セルの端点の符号は個別に接続する。

有限順序付き単体複体と幾何学的実現、単体鎖複体を構成する。
アフィン特異単体を使う自然な比較写像を作り、細分・切除・骨格の帰納法から鎖ホモトピー同値を構成する。
任意係数での Hom による比較と、後の Alexander–Whitney 積の比較まで使える形で公開する。

有限 CW 複体では骨格 \(X^n\)、\(C_n^{\mathrm{cell}}=H_n(X^n,X^{n-1};\mathbb Z)\)、三つの骨格の接続写像からなるセル境界を構成する。
各次数の相対群を向き付きセル上の自由可換群と同定し、境界行列の成分を付着写像の次数として導く。
特異理論との自然な群同型を証明し、任意係数のセル余鎖についても特異コホモロジーとの比較を証明する。
相対セル群が一つの次数に集中することを使う骨格帰納法を基本の証明経路にする。
セル分解を与えた場合には、位相的な付着写像と行列が対応する証明を伴う有限モデルを返す。

## 6. 積・カップ積・係数変更

特異鎖に Alexander–Whitney 写像と shuffle 写像を構成し、Eilenberg–Zilber の鎖ホモトピー同値を証明する。
対角写像との合成から鎖対角を作り、可換環 \(R\) 係数の余鎖の積を定義する。

\[
(\alpha\smile\beta)(\sigma)
=\alpha(\sigma|[0,\ldots,p])\,
\beta(\sigma|[p,\ldots,p+q]).
\]

余鎖レベルでの結合則・単位・自然性と Leibniz 則、交換写像に対応する鎖ホモトピーを証明する。
これによりコホモロジー上の次数付き可換環と環準同型としての引き戻しを構成する。
有限単体モデルでは同じ面の公式で積を計算し、特異余鎖への比較がコホモロジー上の積を保つことを証明する。
セルモデルで積を求める際には、比較済みの単体モデルまたは証明付きのセル対角を与える。

係数準同型による写像と、係数の短完全列から Bockstein 接続写像を構成する。
有限モデルへ移した後に、ホモロジー代数の普遍係数定理・Künneth を適用し、ねじれと係数変更を計算する。
特異鎖の全体は無限ランクでも、有限モデルとの鎖ホモトピー同値または証明済みの係数付き比較によって有限性の仮定を満たす複体へ移す。
コホモロジーの積空間公式は、今回の有限モデルが与えられた空間と係数の条件を明示した形で公開する。

カップ積と有限モデルの標準的な計算は [Hatcher, Algebraic Topology, Chapter 3, §§3.1–3.2](https://pi.math.cornell.edu/~hatcher/AT/ATch3.pdf) と照合する。
細分・切除・セル比較は [同 Chapter 2](https://pi.math.cornell.edu/~hatcher/AT/ATch2.pdf) を照合先とする。

## 7. 計算する空間と完了時の結果

以下は一般定理を適用して得る目標値である。
すべての結果について生成元・関係と元の特異コホモロジーとの同型を公開する。

| 空間・係数 | 計算結果と確認する構造 |
| --- | --- |
| 空空間、任意の係数群 \(A\) | 非負次数の通常コホモロジーは零 |
| 一点、区間、非空可縮空間 | \(H^0\cong A\)、正次数は零 |
| \(S^0\) | \(H^0\cong A\times A\)、正次数は零 |
| \(S^n\)、\(n\ge1\) | \(H^0\cong A\)、\(H^n\cong A\)、他は零、整数係数で次数の写像を計算 |
| 有限グラフ | 成分数 \(c\)、辺数 \(e\)、頂点数 \(v\) に対し \(H^0\cong A^c\)、\(H^1\cong A^{e-v+c}\)、高次は零 |
| \(T^2=S^1\times S^1\)、整数係数 | \(H^0=\mathbb Z\)、\(H^1=\mathbb Z^2\)、\(H^2=\mathbb Z\)、環は次数1の生成元 \(a,b\) の外積代数 |
| \(\mathbb{RP}^2\)、整数係数 | \(H^0=\mathbb Z\)、\(H^1=0\)、\(H^2=\mathbb Z/2\)、高次は零 |
| \(\mathbb{RP}^2\)、\(\mathbb F_2\) 係数 | \(H^*\cong\mathbb F_2[u]/(u^3)\)、\(\deg u=1\)、\(u^2\ne0\) |

有限グラフは有限1次元 CW モデルで扱い、全域森から基底を構成する。
トーラスは円周の積として構成し、二つの射影から得る \(a,b\) と積 \(a\smile b\) の生成性を Künneth と外積から証明する。
積の恒等式 \(a^2=b^2=0\)、\(a\smile b=-b\smile a\) と、因子交換写像の作用を計算する。

実射影平面は球面の反対点を同一視する商と、円板の境界の反対点を貼り合わせるモデルを構成して同相を証明する。
標準のセル構造の境界 \(C_2\to C_1\) が2倍であることを、境界の付着写像の次数から示す。
積については具体的な有限順序付き三角形分割を与えて実現との同相を証明し、Alexander–Whitney 公式で \(u\smile u\) を評価する。
整数の細胞余鎖と \(\mathbb F_2\) の単体余鎖の結果を、それぞれ特異理論へ比較する。
\(0\to\mathbb Z\xrightarrow{2}\mathbb Z\to\mathbb F_2\to0\) の Bockstein が \(H^1(\mathbb{RP}^2;\mathbb F_2)\) の生成元を \(H^2(\mathbb{RP}^2;\mathbb Z)\) の生成元へ送ることも検査する。

\(\mathbb F_2\) は整数の商として環を構成し、必要な体の法則と計算用の二元表現を接続する。
球面の反転、円周の整数次数の写像、トーラスの射影・因子交換について誘導準同型を計算する。
位相空間のモデルや有限表示を変更したときは、比較同型の下で計算結果が一致することを証明する。

## 検査と完了条件

新設する `libs/topology/cohomology_models` に `Basic`、`Relative`、`Excision`、`Spheres`、`Graphs`、`Torus`、`ProjectivePlane`、`Maps` の利用例を設ける。
群だけでなく、代表余鎖・積・誘導写像・相対群の接続写像を別パッケージから検査する。
空空間、非連結空間、零次、ねじれを含む整数係数と標数2の係数を含める。

```sh
cargo build -p cli
cargo run -p cli -- libs/topology/singular_cohomology --module singular_cohomology
cargo run -p cli -- libs/topology/cohomology_models --module cohomology_models
cargo run -p cli -- libs/algebra/homological/concrete_complexes --module concrete_complexes
cargo run -p cli -- libs/topology/cell_spaces --module cell_spaces
cargo run -p cli -- libs/geometry/coordinate_calculus
cargo run -p cli -- libs/std
```

検査は [CLI のキャッシュと範囲選択](../../src/USAGE.md) に従い、新設後のパッケージと利用 project を指定する。
ライブラリの検査は workspace の `libs/refcache/` を共有する。
新規パッケージと具体的な空間の構成を `libs/ref.toml` の `[workspace].packages` に登録する。
各 README と `libs/README.md` に依存・公開 API・計算例・検査手順を反映する。
最終的な完了判定は、特異理論の構成、第7節の全計算、有限モデルとの比較、カップ積と写像の証明が揃うことで行う。
定理は位相空間・係数群・写像・必要な前提を命題内に量化して証明する。
言語・体系の制限に直面した場合は、書きたい形と現在の書き方を100行以内の playground 用の再現例として [gaps.md](../gaps.md) に記録する。
回避する構成も成立しない致命的な制限と判明した場合は、診断と影響範囲を明記して停止する。
