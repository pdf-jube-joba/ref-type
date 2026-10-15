# 位相的 K 理論までの残るライブラリ構成

## 到達点と配置

コンパクト Hausdorff 空間上の複素ベクトル束から \(K^0\) 環を構成し、有限 CW 対の相対群・完全列、Bott の2周期性、球面の K 群の計算まで進める。
実 K 理論、特性類、Chern 指標、一般 CW 空間への拡張は後続の実装単位とする。
各段階は定義・構成・主要定理・利用例がそろう単位として個別の実装計画に切り出す。

既存の基盤と公開 API は [ライブラリ一覧](../../libs/README.md) を参照する。
新設するパッケージと、追加する証明の配置は次のとおりである。

| 配置・パッケージ | 残る担当 |
| --- | --- |
| [algebra/basic](../../libs/algebra/basic/README.md)・`algebra` | 多項式の互除法など、近似・スペクトル分離に必要な代数的補題 |
| [algebra/module_theory](../../libs/algebra/module_theory/README.md)・`module_theory`、[algebra/commutative_algebra](../../libs/algebra/commutative_algebra/README.md)・`commutative_algebra` | 有限生成射影加群と直和因子の追加定理 |
| [algebra/linear_algebra](../../libs/algebra/linear_algebra/README.md)・`linear_algebra` | 行列式、逆行列、Gram–Schmidt、Cayley–Hamilton、部分空間の表示 |
| [topology/topological_algebra](../../libs/topology/topological_algebra/README.md)・`topological_algebra` | 逆行列・直交化の連続性、古典群、Grassmannian、近似、根群の連続性、スペクトル分離 |
| [topology/algebraic_topology](../../libs/topology/algebraic_topology/README.md)・`algebraic_topology` | 円板・球面のコンパクト性と商表示の比較、有限 CW 対の cofibration、cofiber・Puppe 列 |
| `libs/topology/vector_bundles`・`vector_bundles`（新設） | 束、局所自明化、束演算、補束、集合に収まる同型類、ホモトピー不変性 |
| `libs/topology/topological_k_theory`・`topological_k_theory`（新設） | \(K^0\)、相対群、積、完全列、Bott 周期性、計算 |

群完成は `algebra.GroupCompletion`、有限従属分割は `metric_spaces.PartitionOfUnity`、積・商・貼り合わせは `topological_constructions` を使う。
スカラーは `real/basic` の `real` と `complex`、位相は `topology/basic` の `topology` と `topology/metric_spaces` の `metric_spaces` に接続する。
各 `ref.toml` は直接 import する依存を宣言し、`std` 以外で約5,000行を目安に共有基盤から応用への依存で分割する。

## 1. 束の表現と線形代数の補強

最初に、底空間・全空間・射影・ファイバーの線形構造・局所自明化をまとめる束の signature と、商の台集合にできる表示を具体化する。
公開 API は束を受け取り、基底や埋め込みを選ぶデータは比較可能な補助構造にする。
ランクは局所定数として扱い、非連結空間の成分ごとのランク変化を含める。

固定した底空間 \(X\) について、次の方式で束の同型類を集合に収める。

1. 自明束 \(X\times\mathbb C^N\) の連続な射影行列で表す部分束を、各自然数 \(N\) について集合として構成する。
2. 異なる ambient 次元の表示の間に束同型の関係を定める。
3. コンパクト Hausdorff 空間上の有限ランク束がこの表示を持つことを、Hermitian 計量と自明束への埋め込みから証明する。
4. 表示の集合を束同型で割り、演算と引き戻しを降ろす。

異なる次元の表示・引き戻し・商を接続する最小の利用例を先に検査する。
signature 全体を比較する箇所は、具体的な束同型を構成し、同型類上の等式へ渡す。

`linear_algebra` に行列式・逆行列・Gram–Schmidt・Cayley–Hamilton を追加する。
`topological_algebra` では行列式・逆行列の連続性、\(GL_n(\mathbb C)\) の開性、\(U(n)\)、連続な直交化、射影行列の像の局所基底を証明する。
Grassmannian の位相と局所表示をこの層に置き、普遍束は `vector_bundles` に置く。
円板・球面のコンパクト性は有限積と閉部分空間の定理から導き、`algebraic_topology.Euclidean` に接続する。

## 2. ベクトル束と補束

`vector_bundles` の担当は次のとおりである。

| module 群 | 追加する構成・定理 |
| --- | --- |
| `Bundle` / `Morphism` / `Isomorphism` | 束、束写像、束同型、同型による移送 |
| `Trivial` / `LocalTrivialization` / `Transition` | 自明束、局所表示、遷移関数と cocycle |
| `Pullback` / `Restriction` | 引き戻し・制限と恒等・合成の法則 |
| `DirectSum` / `Tensor` / `Dual` | Whitney 和、テンソル積、双対と構造同型 |
| `Gluing` / `Clutching` | 局所データの貼り合わせ、円板の境界による表示 |
| `Metric` / `Complement` | Hermitian 計量、自明束への埋め込みと補束 |
| `Presentation` / `IsomorphismClass` | 射影表示、表示によらない同型類、演算の降下 |
| `Homotopy` / `Stable` | ホモトピックな写像の引き戻しの同型、安定同型 |
| `Grassmannian` / `Universal` | tautological bundle と後続の分類定理への接続 |

コンパクト Hausdorff 空間上の任意の有限ランク複素束が自明束の直和因子になることを、有限従属分割から証明する。
束演算の法則は束同型として示し、同型類上へ降ろす。
区間方向の引き戻しの同型は局所自明性・コンパクト性・貼り合わせから構成する。
安定化と群完成の関係は、束同型による商を構成した後に証明する。

## 3. \(K^0\) と相対理論

`K0` は束の同型類の直和モノイドに `algebra.GroupCompletion` を適用する。
テンソル積から環構造、引き戻しから反変性を得る。
一点と有限離散空間を計算し、\(K^0(\mathrm{pt})\cong\mathbb Z\) とランクの対応を示す。

`Reduced` は基点への制限の核、`Relative` は有限 CW 対の商を用いて構成する。

\[
\widetilde K^0(X)=\ker\bigl(K^0(X)\longrightarrow K^0(\{x_0\})\bigr),
\qquad
K^{-n}(X,A)=\widetilde K^0\bigl(\Sigma^n(X/A)\bigr)
\quad(n\geq0).
\]

\(A=\varnothing\) では基点を付加した \(X_+\) を使う。
非連結空間のランクは局所定数な整数値関数として扱う。

`algebraic_topology` では reduced suspension の誘導写像、円板・球面と suspension・貼り合わせによる表示の同相を整える。
有限 CW 部分複体の包含が cofibration 条件を満たすことを証明し、cofiber・Puppe 列を構成する。
`topological_k_theory` は相対束表示と商空間表示を比較し、束のホモトピー不変性を使って境界写像・負次数の長完全列・Mayer–Vietoris を証明する。
完全性は `algebra.Exact` の語彙で公開する。

## 4. 近似とスペクトル分離

Bott 周期性は clutching 表示から基本積定理を証明し、相対化する経路を採る。
照合先は [Hatcher, Vector Bundles & K-Theory, §§2.1–2.2](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf) とする。
近似の第一案は Stone–Weierstrass 型の証明であり、証明経路を選ぶ際は `analysis/integration` の `integration` を拡充する積分による案とも比較する。

| 必要な成果 | 配置 | 先にそろえるもの |
| --- | --- | --- |
| コンパクト Hausdorff 空間上の実・複素 Stone–Weierstrass 型近似 | `topological_algebra.Approximation` | 実数の多項式・絶対値の近似、有限部分被覆、連続関数の一様ノルム |
| \(X\times S^1\) 上の Laurent 多項式近似 | `topological_algebra.Approximation` | `algebra.LaurentPolynomial` の評価、点の分離、共役による閉性 |
| 複素多項式の根の存在、分離された根群の連続性 | `topological_algebra.PolynomialRoots` | 代数学の基本定理、根の有界性、重複度を含む有限多重集合と係数の対応 |
| 単位円を避けるスペクトルの連続分解 | `topological_algebra.SpectralSeparation` | 多項式の互除法、Cayley–Hamilton、根群の連続性 |
| 束の自己準同型の近似と部分束への分解 | `vector_bundles` | 局所自明化、有限従属分割、行列版の定理 |
| clutching の安定線形化と基本積定理 | `topological_k_theory.Bott` | 束のホモトピー不変性、ブロック行列、スペクトル分解 |

多項式の代数的補題は `algebra`、行列への代入と核の分解は `linear_algebra`、根群と行列族の連続性は `topological_algebra` に置く。
重複根を含む根の集まりについて連続性を証明し、分離された二つの根群から因子多項式を連続に取り出す。
束への貼り合わせは `vector_bundles` が担当する。
近似経路を変更する場合は、必要定理と直接依存も更新する。

## 5. 基本積定理・Bott 周期性・計算

Hopf 線束 \(H\) と \(u=[H]-1\) から、自然な環同型を証明する。

\[
K^0(X)[u]/(u^2)\cong K^0(X\times S^2).
\]

そこから Bott 元 \(\beta\in\widetilde K^0(S^2)\) との外積による自然な同型を得る。

\[
\widetilde K^0(X)\xrightarrow{\;\beta\,\smile\,-\;}
\widetilde K^0(S^2\wedge X).
\]

写像についての自然性、相対理論との整合性まで証明し、全整数次数への周期化、積の符号規則、6項完全列を公開する。
基本積定理から周期性への照合先は上記参考書の Theorems 2.2 and 2.11 とする。

\(m\geq0\) に対して球面の群を計算する。

\[
\widetilde K^0(S^{2m})\cong\mathbb Z,
\qquad
\widetilde K^0(S^{2m+1})=0,
\qquad
K^{-1}(\mathrm{pt})=0.
\]

偶数次球面では Bott 元の反復積と生成元の対応も示す。
Hopf 線束と \(S^2\) の環構造、有限 CW 空間への完全列の適用、空空間・零ランク・非連結空間を利用例に含める。

## 依存方向と公開 API

追加する主な依存方向は、基盤を提供する側から利用側へ次のようにする。

`topological_algebra`・`metric_spaces`・`topological_constructions`・`linear_algebra` → `vector_bundles` → `topological_k_theory`。

束のホモトピー不変性には `algebraic_topology`、\(K^0\) には `algebra`、相対 K 理論には `algebraic_topology` を直接依存として加える。
加群に関する定理を使う箇所は `module_theory`・`commutative_algebra` に接続する。
定理は底空間・束・数学的条件を命題内で量化し、構成のデータと法則は `\structure` にまとめる。

圏・関手の公開 API を利用側に置き、必要なパッケージが `category` を直接依存に加える。
対象集合を固定した空間の族で関手を作り、一般の空間には引き戻しの恒等則・合成則を直接量化して公開する。
全空間を対象とする圏の表現は別の設計課題とする。

## 後続のライブラリ分け

| 発展方向 | 配置・担当 | 追加する内容 |
| --- | --- | --- |
| \(KO\) と8周期性 | `vector_bundles.Real`、`topological_k_theory.Real` | 実束、実・複素化、Clifford 代数・加群、独立した周期性の証明 |
| Chern 類・Chern 指標 | 新規 `libs/geometry/characteristic_classes`、`topological_k_theory.ChernCharacter` | 特異コホモロジー、射影束、分裂原理、有理係数 |
| \(\lambda\)・Adams 演算 | `linear_algebra`、`vector_bundles`、`topological_k_theory.Operations` | ベクトル空間・束の外冪、分裂原理 |
| 一般 CW 空間 | `algebraic_topology`、`vector_bundles`、`topological_k_theory` | 一般のセル付着、局所有限被覆・パラコンパクト性、分類空間、逆極限・\(\lim^1\) |
| コンパクト台付き K 理論 | `topology`、`topological_k_theory.CompactSupport` | 一点コンパクト化、固有写像、相対化 |
| 同変 K 理論 | 新規 `representation_theory`・`equivariant_topology`、K 理論側の module | 群作用、コンパクト群の表現、同変束と周期性 |
| Fredholm・作用素による K 理論 | 新規 `functional_analysis`・`operator_algebras` | Hilbert 空間、有界・コンパクト・Fredholm 作用素、作用素環 |
| 指数定理 | `geometry/manifolds`・`geometry/euclidean_forms`・`geometry/differential_forms`、新規 `index_theory` | 滑らかな束・楕円型作用素、`calculus`・`integration` と関数解析の拡充 |
| スペクトラムによる表現 | 新規 `stable_homotopy` と K 理論側の module | 安定ホモトピー圏、スペクトラム、表現可能性 |

Chern 指標は [特異コホモロジー計画](singular-cohomology.md) と特性類を前提にする。
通常のコホモロジーの代数的基盤は `algebra/homological` の分割を使い、残る比較・自然性・Künneth は [ホモロジー代数計画](homological-algebra.md) で整える。
既存の `linear_algebra` の交代形式・外積は、束の外冪を構成する際の代数的基盤として利用する。

## 検査と各段階の完了条件

| 段階 | 完了条件 |
| --- | --- |
| 1 | 異なる次元の射影表示・引き戻し・商の最小例、連続な逆行列・直交化、局所基底、円板・球面のコンパクト性 |
| 2 | 束演算、補束、任意の対象範囲内の束の射影表示、表示の独立性、ホモトピー不変性 |
| 3 | \(K^0\) 環、相対表示の比較、境界写像、負次数の完全列と自然性 |
| 4 | パラメータ付き clutching の近似・スペクトル分解とホモトピーとの整合性 |
| 5 | 自然な Bott 同型と相対化、全次数・6項完全列、球面の群と生成元の計算 |

束の表現、補束、近似の完成時に型検査時間と証明の粒度を確認し、パッケージ分割を更新する。
新規パッケージに `ref.toml`・`src/root.ref`・README を用意し、`libs/ref.toml` の `[workspace].packages` と `libs/README.md` に追加する。
[libs/topology/cell_spaces](../../libs/topology/cell_spaces/src/root.ref) に、束の引き戻し、補束、Hopf 線束、相対群、球面の計算を追加する。

検査は [CLI のキャッシュと範囲選択](../../src/USAGE.md) に従い、変更したパッケージと利用 project を指定する。
ライブラリの検査は workspace の `libs/refcache/` を共有する。
新設後の検査例は次のとおりである。

```sh
cargo build -p cli
cargo run -p cli -- libs/topology/vector_bundles --module vector_bundles
cargo run -p cli -- libs/topology/topological_k_theory --module topological_k_theory
cargo run -p cli -- libs/topology/cell_spaces --module cell_spaces
cargo run -p cli -- libs/std
cargo run -p cli -- libs/category
```

言語・体系の制限に直面した場合は、書きたい形と現在の書き方を100行以内の playground 用の再現例として [gaps.md](../gaps.md) に記録する。
回避する構成も成立しない致命的な制限と判明した場合は、診断と影響範囲を明記して停止する。
