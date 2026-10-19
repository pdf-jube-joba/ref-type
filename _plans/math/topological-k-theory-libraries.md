# 位相的 K 理論までのライブラリ

コンパクト Hausdorff 空間の複素ベクトル束から \(K^0\) 環を構成し、有限 CW 対の相対理論・Bott の2周期性・球面の計算へ進む。
各節を定義・主要定理・利用例がそろう実装計画に切り出す。

## 配置

| package | 担当 |
| --- | --- |
| `algebra` / `linear_algebra` | 多項式の互除法、行列式・逆行列・Gram–Schmidt・Cayley–Hamilton |
| `topological_algebra` | 逆行列・直交化の連続性、古典群、Grassmannian、近似とスペクトル分離 |
| `algebraic_topology` | 円板・球面のコンパクト性と商表示、CW cofibration、cofiber・Puppe 列 |
| 新規 `vector_bundles` | 束、局所自明化、演算、補束、同型類、ホモトピー不変性 |
| 新規 `topological_k_theory` | \(K^0\)、相対群、積、完全列、周期性、計算 |

基盤は [ライブラリ一覧](../../libs/README.md) を参照。
有限従属分割は `metric_spaces`、積・商・貼り合わせは `topological_constructions`、群完成は `algebra.GroupCompletion` を使う。
依存は基盤から `vector_bundles`、そこから `topological_k_theory` へ向ける。

## 1. 束の表現と線形代数

底空間・全空間・射影・線形構造・局所自明化を signature にまとめ、ランクは局所定数とする。
固定した底空間について、各 \(N\) の自明束 \(X\times\mathbb C^N\) の連続な射影行列を表示の集合にする。
異なる ambient 次元間の束同型を定義し、その商へ演算と引き戻しを降ろす。
任意の有限ランク束がこの表示を持つことを、Hermitian 計量と自明束への埋め込みから示す。

先に異なる次元の表示・引き戻し・商の最小例を検査する。
線形代数を補強し、\(GL_n(\mathbb C)\) の開性、\(U(n)\)、射影の像の局所基底、Grassmannian の位相を構成する。

## 2. 束演算と補束

局所データの貼り合わせ・clutching、引き戻し・制限、直和・テンソル・双対を構成し、束同型として法則を示す。
有限従属分割で任意の束が自明束の直和因子になることを証明する。
区間方向の引き戻しの同型を局所自明性・コンパクト性・貼り合わせから構成する。
同型類、安定同型、群完成の対応と tautological bundle を公開する。

## 3. 相対 K 理論

束の同型類の直和モノイドを群完成し、テンソル積で環、引き戻しで反変関手にする。
一点と有限離散空間の群を計算し、非連結空間のランクは局所定数な整数値関数として扱う。

\[
\widetilde K^0(X)=\ker\bigl(K^0(X)\to K^0(\{x_0\})\bigr),
\qquad K^{-n}(X,A)=\widetilde K^0(\Sigma^n(X/A)),\quad n\ge0.
\]

\(A=\varnothing\) は \(X_+\) を使う。
CW 部分複体の cofibration、reduced suspension の写像、cofiber・Puppe 列を整え、相対束表示と商空間表示を比較する。
ホモトピー不変性から境界写像、負次数の長完全列、Mayer–Vietoris と自然性を証明する。
完全性は `algebra.Exact` で公開する。

## 4. 近似とスペクトル分離

clutching 表示から基本積定理を示す経路を採る。

1. 実数の多項式・絶対値の近似と一様ノルムから、コンパクト Hausdorff 空間の実・複素 Stone–Weierstrass 型近似を示す。
2. Laurent 多項式の評価・点の分離・共役の閉性を使い、\(X\times S^1\) 上の近似を得る。
3. 代数学の基本定理、根の有界性・重複度を持つ有限多重集合と係数の対応から、分離された根群と因子多項式の連続性を示す。
4. 互除法・Cayley–Hamilton を使い、単位円を避けるスペクトルを連続に分解する。
5. 局所自明化と有限従属分割で束の自己準同型へ移し、clutching の安定線形化を得る。

根群・行列族の連続性は `topological_algebra`、束への貼り合わせは `vector_bundles` に置く。
近似経路は `integration` を拡充する積分による案とも比較する。

## 5. Bott 周期性と計算

Hopf 線束 \(H\) と \(u=[H]-1\) により

\[
K^0(X)[u]/(u^2)\cong K^0(X\times S^2)
\]

を示し、Bott 元 \(\beta\) との外積による自然な同型

\[
\widetilde K^0(X)\xrightarrow{\beta\smile-}\widetilde K^0(S^2\wedge X)
\]

を得る。
照合先は [Hatcher, §§2.1–2.2, Theorems 2.2 / 2.11](https://pi.math.cornell.edu/~hatcher/VBKT/VB.pdf)。
相対化、全整数次数への周期化、積の符号、6項完全列を公開する。
\(m\ge0\) について

\[
\widetilde K^0(S^{2m})\cong\mathbb Z,\qquad
\widetilde K^0(S^{2m+1})=0,\qquad K^{-1}(\mathrm{pt})=0
\]

を計算し、反復 Bott 積と偶数次の生成元を対応させる。
[cell_spaces](../../libs/topology/examples/cells/src/root.ref) に引き戻し・補束・Hopf 線束・相対群・球面、空空間・零ランク・非連結空間の利用例を置く。

## 公開と検査

定理の対象と仮定は命題内で量化し、構成のデータと法則は structure にまとめる。
集合に収まる空間族では `category` の API を使い、一般の空間には引き戻しの恒等・合成則を直接公開する。
新規 package は約5,000行を目安に分け、直接依存・workspace member・README を更新する。
検査には [共有キャッシュ](../../src/USAGE.md#検査とキャッシュ) を使う。
各節の構成・比較・自然性と利用例がそろった時点を完了とする。

後続は実 K 理論と8周期性、特性類・Chern 指標、外冪・Adams 演算、一般 CW 空間、コンパクト台付き・同変・作用素 K 理論、指数定理、スペクトラムによる表現。
Chern 指標は [特異コホモロジー](singular-cohomology.md) と特性類を前提にする。
