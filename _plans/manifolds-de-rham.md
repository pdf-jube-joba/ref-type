# 多様体と De Rham コホモロジーの定義

## 到達点

境界のない有限次元実滑らかな多様体を、Hausdorff・第二可算な位相空間と滑らかなアトラスから構成する。
滑らかな写像、微分同相、接空間・余接空間、微分形式、外積、外微分、引き戻しを定義し、De Rham 複体と各次数の実ベクトル空間 \(H^k_{\mathrm{dR}}(M)\) を実際に構成する。
完了条件は、外微分の二乗零、座標表示の独立性、コホモロジー上の積と引き戻しの well-definedness まで証明して、別パッケージの具体例から利用できることである。

対象の次元 \(n\) は自然数として固定し、零次元と空多様体も扱う。
非連結多様体にも同じ次元を用いる。
境界付き多様体、微分形式の積分、Stokes の定理、Poincaré の補題、特異コホモロジーとの De Rham 同型定理は、この基盤の上に置く後続の実装単位とする。

この文書全体を一つの実装計画とし、以下の段階は依存関係に沿った中間検査点とする。

## 実装状況（2026-10-08）

第1節から第8節までの数学的構成と証明を実装した。
`tests/projects/manifolds-de-rham` 全体のキャッシュなし検査が成功し、すべての利用例を依存ライブラリの証明本体とともに検査した。

| 段階 | 主な公開 API | 検査した構成と法則 |
| --- | --- | --- |
| 開集合上の微分法 | `calculus.Real.Limit`、`Derivative`、`MeanValue`、`Multivariable.Open`、`Maps`、`Schwarz` | 極限と微分の演算、最大値ノルムと座標位相、第二可算性、局所性、全微分・連鎖律、混合偏微分の交換 |
| 外代数と商 | `linear_algebra.Field.Space.Exterior`、`FiniteExterior`、`Quotient`、`algebra.Module` | shuffle による任意次数の外積、有限基底の増加添字による係数復元、次元超過の零性、部分加群・商の普遍性 |
| アトラスと多様体 | `manifolds.Dimension.Chart`、`Atlas`、`Smooth`、`SmoothMap`、`SmallAtlasSmoothMap` | Hausdorff・第二可算な多様体、飽和・最大性・冪等性、滑らかな写像・微分同相、小さいアトラスでの判定 |
| 接空間と微分 | `manifolds.Tangent`、`Differential`、`DifferentialIdentity`、`DifferentialComposition`、`OpenSubmanifold` | 接ベクトルの商と座標同型、余接空間、標準微分の代表独立性、恒等・合成・開部分多様体・微分同相との整合性 |
| 局所形式 | `differential_forms.Euclidean.On`、`Euclidean.Pullback` | 滑らかな係数表示と復元、外微分の係数公式、\(d^2=0\)、Leibniz 則、引き戻しの合成・自然性 |
| 大域形式 | `differential_forms.Forms.On`、`Pullback`、`Restriction`、`Gluing`、`AtlasForms`、`Presentation` | 座標の独立性、点ごとの交代形式との双方向の対応、任意の開被覆での一意な貼り合わせ、アトラス間の線形同型 |
| De Rham コホモロジー | `homological_algebra.Cochain.Over`、`Forms.On.DeRham`、`PullbackDiffeomorphism` | 整数次数への零拡張、核・像の商、\(H^0\) と微分が零の滑らかな関数の同型、代表によらない積と環の法則、反変性、微分同相・アトラス表示による同型 |
| 独立した利用例 | `tests/projects/manifolds-de-rham` | 空・一点・開部分集合、\(x\,dy\)、非線形な shear、二つのチャート、小さいアトラスと飽和、表示の比較、形式とコホモロジーの反変な合成則 |

点・次数に依存する型の具体化、record の帰納法、検査済み定義の参照と capture、namespace の共有、未解決変数の探索を処理系で修正した。
表現の変更で回避した制約と最小例は [G09–G16](gaps.md) に記録した。

第8節の最終検査はすべて成功した。
全11パッケージと3 project をキャッシュなしで検査し、Rust ライブラリ253件と、新 project を含む CLI 全30件のテストが成功した。
CLI のビルド、Rust の書式検査、差分の空白検査も成功した。

## 計画時の調査（2026-10-07）

2026-10-07 時点のソースを調査した結果である。
ここでの「既存」は宣言・証明本体の所在を確認したという意味で、今回の計画作成ではライブラリ全体の再検査は実行していない。

| 層 | 既存の実装 | 追加するもの |
| --- | --- | --- |
| 実数解析 | `real.Analysis` の体、距離、評価、数列、Dedekind 実数の完備性 | 極限の一意性と演算、局所的な微分則、平均値定理に必要な補題 |
| 微分 | `calculus.Real.Derivative`、`Real.Multivariable` の偏微分・全微分・反復偏微分による滑らかさ | 開集合上の微分、ベクトル値写像、連鎖律、連続偏微分からの全微分、Schwarz の定理 |
| 位相 | `topology.Topology` の Hausdorff 性・第二可算性、`Subspace`、`Homeomorphism`、`Gluing` | 有限実座標空間の第二可算性、開部分空間の性質、チャートの定義域を追跡する API |
| 座標空間 | `topological_algebra.Coordinates`、`FiniteDimensional` の座標位相と線形写像の連続性 | `calculus` の最大値ノルムによる連続性との接続 |
| 線形代数 | `linear_algebra.Field.Space` の線形写像・双対・部分空間・有限和・双線形形式・テンソル積 | 任意次数の交代多重線形形式、外積、像部分空間、商ベクトル空間 |
| 商と完全性 | `std.Set.Quotient`、`algebra.Quotient`、`algebra.Exact` の商演算と核・像 | 次数付きの余鎖複体、コホモロジー、余鎖写像による降下 |
| 多様体 | 専用パッケージは現在存在しない | アトラス、滑らかな写像、接空間、微分形式、De Rham 複体 |

特に `calculus.Real.Multivariable.Smooth.Def.Smooth` は \(\forall k\, C^k\) という命題で、対象は \(\mathbb R^n\) 全体で定義された実数値関数である。
`CommutingPartials` と `MixedPartialsCommute` は交換可能性を表す条件として定義されており、滑らかさからそれを導く一般定理は追加が必要である。
現在の `Differential.Def.LinearMap` は実数値線形写像なので、異なる次元間のヤコビアンには既存の一般線形代数との統合が必要になる。

## ライブラリの分担

以下の表は実装した公開 API の分担を示す。
公開する数学的構造を基準に分割し、具体化の都合による小さな補題はその構造の子 module に置く。

| パッケージ | 主な追加先 | 役割 |
| --- | --- | --- |
| `std` | `Data.FinSet`、`Data.List` 周辺 | 有限添字の削除・挿入、置換・shuffle と符号に必要な組合せ論 |
| `topology` | `Topology.Subspace.Properties`、`Topology.Countability` 周辺 | 第二可算性の開部分空間への継承、開集合・局所同相の補題 |
| `topological_algebra` | `Euclidean.Dimension` | \(\mathbb R^n\) の位相、最大値距離との一致、Hausdorff 性・第二可算性 |
| `calculus` | `Real.Limit`、`Real.MeanValue`、`Real.Multivariable.Open`、`Maps`、`Schwarz` | 開集合上の解析と滑らかな写像の微分法 |
| `linear_algebra` | `Field.Space.Multilinear`、`Exterior`、`FiniteExterior`、`Subspace`、`Quotient` | 外代数と商ベクトル空間 |
| `homological_algebra`（新設） | `Cochain.Over`、`Over.At`、`Over.Map` | 体上の余鎖複体とコホモロジーの一般構成 |
| `manifolds`（新設） | `Dimension`、`SmoothMap`、`Diffeomorphism`、`Tangent`、`Differential`、`OpenSubmanifold`、`Examples` | 位相多様体・滑らかな多様体とその写像 |
| `differential_forms`（新設） | `Euclidean`、`Forms`、`Pullback`、`Restriction`、`Gluing`、`AtlasForms`、`Presentation` | 局所形式の貼り合わせと De Rham コホモロジー |

`calculus` に `linear_algebra`・`topology`・`topological_algebra` への依存を加え、座標と線形写像の既存構造を共有する。
`topological_algebra` の位相・距離の同値性は同パッケージで証明し、それを `calculus` が利用する向きにする。
`homological_algebra` の一般加群・複体の構成と依存は [ホモロジー代数計画](homological-algebra.md) に統合する。
同パッケージは `std`・`algebra`・`category` に依存し、体上の余鎖複体はその具体化として利用する。
`manifolds` は `std`・`real`・`linear_algebra`・`topology`・`topological_algebra`・`calculus` に依存する。
`differential_forms` はこれらと `manifolds`・`homological_algebra` に依存し、`manifolds` からの逆向きの依存は生じない構成とする。
各 `ref.toml` はソースから直接 import するパッケージを依存として宣言する。

## 1. 開集合上の微分法

### 開集合と写像

\(E_n=\mathrm{Fin}(n)\to\mathbb R\) を共通の座標空間とする。
開集合 \(U\subseteq E_n\) は集合と開性を持つ `OpenSet` にまとめ、`Carrier U` はその部分集合型として返す通常の定義にする。
写像は \(U\to V\) を表す構造、または \(U\to E_m\) の関数と値域条件で表し、制限・値域制限・合成を提供する。
極限と微分の近傍条件には、変化させた点が定義域に属する条件を含める。
局所一致による極限・微分の移送、開集合への制限、開被覆からの局所性を証明する。

有限座標の最大値ノルムの三角不等式・斉次性・正定値性、各座標の評価、有限次元線形写像のノルム評価を整える。
座標位相とこの距離位相を同一視し、既存の ε–δ 連続性と位相的連続性の同値を証明する。
有理数を端点とする有限開矩形を用いて可算基を構成する。
零次元の場合は一点空間として各構成を検査する。

### 証明の順序

1. 実数値極限の一意性、和・積・合成、微分可能性から連続性、導関数の一意性を証明する。
2. 一変数の和・積・合成の微分則を証明する。
3. 閉区間のコンパクト性と実数の完備性から極値の存在を整え、Fermat、Rolle、平均値定理を証明する。
4. 各座標について平均値評価を適用し、連続な偏導関数を持つ関数の全微分を構成する。
5. ベクトル値全微分を成分ごとに定義し、一意性、線形写像の微分、連鎖律、ヤコビアンの合成則を証明する。
6. 反復偏導関数の族で `ContDiffOn` と `SmoothOn` を定義し、制限・貼り合わせ・和・積・合成・偏微分についての閉性を証明する。
7. 小さい開矩形で二重差分に平均値定理を適用し、二階偏導関数の連続性から Schwarz の定理を証明する。

`SmoothOn` の有限階の証人は、導関数の一意性を用いて次数間で整合することを示す。
導関数を値として返す演算は、滑らかな関数を入力とする一意な微分の関係から構成し、異なる証人から得た結果が一致することを証明する。
全空間の場合には既存の `Smooth` と新しい定義の同値を示し、既存の定数・座標射影の利用例を接続する。

完了時には、一般の \(U\subseteq E_n\)、\(V\subseteq E_m\)、\(W\subseteq E_l\) に対する滑らかな写像の合成と微分が利用できる。
Schwarz の定理は後の \(d^2=0\) と引き戻しの自然性の証明に使う。

## 2. 外代数と商ベクトル空間

体上のベクトル空間を受け取り、\(k\) 個の引数を持つ多重線形形式と交代形式を定義する。
引数列は \(\mathrm{Fin}(k)\to V\) で表し、零引数の形式はスカラーと同型になるようにする。
交代性は二つの異なる引数位置に同じベクトルを入れたとき零になる条件から定め、置換の符号に従う変換則を証明する。

外積は shuffle による有限和で構成し、双線形性、単位、結合則、次数付き可換則を証明する。
線形写像による前合成と外積の整合性を証明する。
有限次元では増加添字列による係数表示と復元を証明し、\(k>n\) の交代形式が零になることを得る。
実装に必要な有限列・符号・和の補題はこの段階で揃える。

部分空間について零部分空間、像、逆像、包含を整備する。
商 \(V/W\) は \(v\sim w\iff v-w\in W\) による `std.Set.Quotient` の具体化として作り、加法・スカラー倍・商写像・線形写像の降下と普遍性を証明する。
一般の商加群は [ホモロジー代数計画の第1節](homological-algebra.md#1-加群自由加群商) が所有し、ここでは体上への具体化を公開する。
部分空間 \(B\subseteq Z\subseteq V\) の場合に、\(B\) を \(Z\) の部分空間へ移す構成を公開する。

## 3. アトラスと滑らかな多様体

`Chart` は \(M\) の開集合 \(U\)、\(E_n\) の開集合 \(V\)、部分空間間の同相 \(\varphi:U\to V\) をまとめる。
チャートの重なりは \(U_i\cap U_j\) から作り、遷移写像の定義域を \(\varphi_i(U_i\cap U_j)\) とする。
この集合の開性と、遷移写像が \(\varphi_j\circ\varphi_i^{-1}\) であることを型と法則で追跡する。

`TopologicalManifold` は台集合・位相・次元・チャートの被覆・Hausdorff 性・第二可算性をまとめる。
`SmoothAtlas` は被覆とすべての順序付きチャート対の滑らかな遷移写像を持つ。
あるアトラスと互換な全チャートを集め、その飽和が滑らかな最大アトラスになることを、制限・合成・滑らかさの局所性から証明する。
`SmoothManifold` はこの最大アトラスを持つ構造として公開し、小さいアトラスからの構成関数を提供する。
同じ最大アトラスを生成する二つの表示について、恒等写像が微分同相となり、後の形式空間とコホモロジーが標準的に同型となることを示す。

`SmoothMap` は写像・連続性・局所座標表示の滑らかさを持つ。
連続性から \(U_i\cap f^{-1}(U_j)\) の開性を得て座標表示を作る。
選んだ被覆上での判定と最大アトラスでの判定の同値を証明する。
恒等写像・合成・開部分多様体への制限を構成し、`Diffeomorphism` は逆向きの滑らかな写像と逆の法則を持つ構造にする。

具体例として \(E_n\)、その任意の開部分集合、一点多様体、空多様体を構成する。
重なりを持つ二つのチャートと非恒等の座標変換も検査し、アトラスの飽和と制限の往復を確認する。

## 4. 接空間・余接空間と微分

点 \(x\) における接ベクトルを、\(x\) を含むチャート \(\varphi\) と座標ベクトル \(v\in E_n\) の対の同値類として構成する。
関係は次で定める。

\[
(\varphi,v)\sim(\psi,w)
\quad\Longleftrightarrow\quad
w=D(\psi\circ\varphi^{-1})_{\varphi(x)}v.
\]

連鎖律と遷移写像の逆の法則から同値関係を証明する。
共通のチャートへ移して加法・スカラー倍を定義し、代表によらないことを示して \(T_xM\) を実ベクトル空間にする。
各チャートから得る \(T_xM\cong E_n\) と、その双対としての \(T_x^*M\) を公開する。
滑らかな写像の微分 \(T_xf:T_xM\to T_{f(x)}N\) をヤコビアンから降ろし、恒等写像・合成・微分同相との整合性を証明する。
点に依存する台集合は通常の型値定義で公開し、局所点を module 具体化に渡す必要を減らす。

接束・余接束の全空間の位相と一般ベクトル束の局所自明性は、これらの座標同型から拡張する後続の単位とする。
今回の微分形式は次の座標による貼り合わせで構成し、点ごとの交代形式による解釈まで接続する。

## 5. 開集合上の微分形式

\(U\subseteq E_n\) 上の \(k\)-形式を、交代 \(k\)-形式の族であって標準基底で評価した係数が滑らかなものとして定義する。
第2段階の係数表示により、増加添字列 \(I\) を用いた次の表示と同値であることを示す。

\[
\omega=\sum_{i_1<\cdots<i_k}\omega_{i_1\cdots i_k}\,
dx^{i_1}\wedge\cdots\wedge dx^{i_k}.
\]

形式の等式は各点・各引数での等式により判定できるようにする。
零次形式と滑らかな実数値関数の同型、\(k>n\) の形式空間が零空間になることを証明する。
係数ごとの和・スカラー倍、点ごとの外積、開集合への制限を構成する。

外微分を次の係数公式で定義し、滑らかさを証明する。

\[
d\omega=\sum_I\sum_{j=1}^n
\frac{\partial\omega_I}{\partial x^j}\,dx^j\wedge dx^I.
\]

線形性、零次での全微分との一致、次数付き Leibniz 則を証明する。
Schwarz の定理と外積の交代性から \(d^2=0\) を導く。
\(F:U\to V\) による引き戻しは \((F^*\omega)_x(v_1,\ldots,v_k)=\omega_{F(x)}(DF_xv_1,\ldots,DF_xv_k)\) とし、係数が滑らかなことを示す。
連鎖律から合成則を、係数公式・積の微分則・Schwarz の定理から \(d(F^*\omega)=F^*(d\omega)\) を証明する。

この局所構成から多様体へ進む設計は、[Sadun, Lecture Notes on Differential Forms](https://arxiv.org/abs/1604.07862) の座標公式と座標変換を先に扱う構成を参考にする。

## 6. 多様体上の微分形式と外微分

最大アトラスの各チャートの像に局所形式 \(\omega_i\) を割り当て、重なり上で次を満たす族を \(\Omega^k(M)\) とする。

\[
\omega_i=(\varphi_j\circ\varphi_i^{-1})^*\omega_j
\quad\text{on }\varphi_i(U_i\cap U_j).
\]

小さいアトラス上の互換な族から一意に最大アトラスへ拡張できることを証明する。
任意の開被覆に関する制限と互換な形式の一意な貼り合わせも公開する。
この構成により、開被覆に沿う等式判定と座標表示の独立性を得る。
第4段階の座標同型を用い、局所形式の族と、各 \(x\) での \(T_xM\) 上の交代形式を滑らかに割り当てるものとの双方向の対応を証明する。

加法・スカラー倍・外積は局所的に定義して互換性を証明する。
外微分は各チャートでの \(d\omega_i\) とし、局所引き戻しとの可換性から貼り合わせ条件を証明する。
\(\Omega^k(M)\) の実ベクトル空間構造、\(d\) の線形性・二乗零・次数付き Leibniz 則を公開する。

一般の滑らかな写像 \(f:M\to N\) の引き戻しは、始域のチャートを \(f\) の像が終域のチャートに入る開集合で細分して定義し、一意に貼り合わせる。
チャートの選択によらないこと、線形性、恒等写像・合成・外積・外微分との整合性を証明する。

## 7. 余鎖複体と De Rham コホモロジー

`homological_algebra` に、自然数次数のベクトル空間族 \(C^k\)、線形写像 \(d_k:C^k\to C^{k+1}\)、二乗零の法則を持つ `CochainComplex` を定義する。
内部では [ホモロジー代数計画の第2節](homological-algebra.md#2-複体ホモロジーホモトピー) の整数次数の加群複体を用い、負次数を零で埋めた非負次数の API として公開する。
次数によって台集合が変わる族は宣言の束を用いて表現し、通常の値 record が必要な部分は次数ごとのデータに分ける。
余鎖写像、恒等写像、合成とコホモロジー上の誘導線形写像を構成する。

\[
Z^k(C)=\ker d_k,\qquad
B^0(C)=\{0\},\qquad
B^{k+1}(C)=\operatorname{im}d_k,\qquad
H^k(C)=Z^k(C)/B^k(C).
\]

二乗零から \(B^k(C)\subseteq Z^k(C)\) を証明し、第2段階の商ベクトル空間へ接続する。
次数零は上の定義で直接扱い、自然数の切り詰め減算による前次数の表現を避ける設計にする。
閉形式の類、類の等式判定、完全形式の類が零になること、商の普遍性を公開する。

`differential_forms.DeRham` で、第6段階で構成した形式空間と外微分からこの複体を具体化する。
`Closed`、`Exact`、`cohomology`、`classOf`、`pullback` を多様体と次数を入力として使える形で公開する。
\(H^0_{\mathrm{dR}}(M)\) は \(df=0\) を満たす滑らかな関数の空間と同型になることを証明する。

閉形式の外積が閉形式であることと、完全形式と閉形式の外積が完全であることから、コホモロジー上の積を降ろす。
後者は両方の代表を変更する場合まで示し、次数付き可換性・結合則・単位を得る。
滑らかな写像の引き戻しが誘導する
\(f^*:H^k_{\mathrm{dR}}(N)\to H^k_{\mathrm{dR}}(M)\) について、恒等写像・合成・積の法則と、微分同相による同型を証明する。

多様体・微分形式・コホモロジーの標準的な定義と法則の照合先は、[Michor, Topics in Differential Geometry, Chapters I・III](https://lu.math.uci.edu/pdfs/lecture_notes/Math-240BC/dgbook.pdf) とする。

## 8. 利用例と完了検査

`tests/projects/manifolds-de-rham` を作り、次の例を独立した module に分けて検査する。

| 例 | 検査する接続 |
| --- | --- |
| 空多様体と一点多様体 | 空のチャート族、零次元、一点の \(H^0\cong\mathbb R\) と正次数の零性 |
| \(E_n\) と開部分集合 | 標準アトラス、制限、\(\Omega^0\) と滑らかな関数、\(k>n\) の零性 |
| \(\mathbb R^2\) の形式 \(x\,dy\) | \(d(x\,dy)=dx\wedge dy\)、\(d^2=0\)、\([dx\wedge dy]=0\) |
| \(F(u,v)=(u,v+u^2)\) | 非線形な微分同相、ヤコビアン、\(F^*(dy)=dv+2u\,du\)、外微分との可換性 |
| 恒等チャートと \(F\) による二つのチャート | 重なりの変換則、接ベクトルの代表変更、同じ大域形式の異なる座標表示 |
| 小さいアトラスとその飽和 | 形式の一意な拡張、形式空間・De Rham コホモロジーの同型 |
| 滑らかな写像の合成 | 形式とコホモロジーの両方で反変な合成則を利用できること |

実装した各段階で当該パッケージと利用側を `--no-cache` で検査する。
最終段階では新しい project を `src/cli/tests/ref_files.rs` の既存の project 検査に登録し、依存を変更した既存 project も含めて確認する。

```sh
cargo build -p cli
for package in std algebra real complex linear_algebra topology topological_algebra calculus homological_algebra manifolds differential_forms; do
  target/debug/cli "libs/$package" --no-cache --diagnostics compact || exit 1
done
target/debug/cli tests/projects/manifolds-de-rham --no-cache --diagnostics compact
target/debug/cli tests/projects/library --no-cache --diagnostics compact
target/debug/cli tests/projects/topological-k-theory --no-cache --diagnostics compact
cargo test -p cli --test ref_files --locked
```

新設パッケージの README、`libs/README.md` の依存表・検査手順、変更した既存 API の利用例を更新する。
最終的な検査結果と実装済みの公開 API をこの計画へ反映する。

## 表現上の注意と実装順の判断

数学的対象は位相空間・ベクトル空間・開集合・多様体としてまとめて受け取り、台集合と法則をばらばらに渡す API を整理する。
構成は `\definition` を基本とし、データと法則は `\structure` でまとめる。
計算可能な有限添字の処理では既存の Program と `\machine`・`\correspondence` の仕組みを使い、実行と数学的仕様を接続する。
定理は前提を含む命題全体を量化した証明として定義する。

動く次数・次元・点に依存する型には、[G05](gaps.md#g05) の回避に使われている型値の通常の定義を適用する。
関係を parameter に持つ集合値 record には、必要に応じてデータ・法則・部分集合型を分ける [G03](gaps.md#g03) の既存パターンを使う。
導関数や商の降下の値は、法則を持つ入力と一意性の証明から構成する。
局所形式の族、接空間の商、次数付き複体については、最初に小さな利用側 module まで含めて型の受け渡しを検査し、その後に一般証明を展開する。

有限積のコンパクト性には [G06](gaps.md#g06) の既知の具体化問題がある。
本計画の解析では一変数閉区間のコンパクト性と有限座標の評価を使うため、この問題の影響範囲を実装時に確認する。
一般定理の具体化が失敗した場合は、必要な型の受け渡しだけに縮小した再現例を作る。
言語や体系に由来する障害が判明した場合は、書きたい構成・再現例・診断・影響する段階を `gaps.md` に記録し、等価な表現または処理系の修正を検査する。
回避を含めて構成が不可能な場合に限り、その理由を明記して停止する。
数学的な補題の不足は上の依存順に組み込み、最後のコホモロジーと利用例まで実装を続ける。
