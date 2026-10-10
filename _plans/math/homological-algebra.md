# ホモロジー代数の基盤と有限複体の計算

## 到達点と他の計画との関係

可換環上の加群を基礎に、鎖複体・余鎖複体、ホモロジー、鎖ホモトピー、長完全列、射影分解、Ext・Tor を構成する。
有限自由整数複体について、普遍係数定理、Künneth の定理、Smith 標準形によるホモロジー・コホモロジーと誘導写像の計算まで実装する。
一般の理論と有限行列による計算を接続し、計算結果は元の核を像で割った加群との同型として返す。

[特異コホモロジー計画](singular-cohomology.md) はこの基盤を使って位相空間のコホモロジーを計算する。
[De Rham コホモロジー](../../libs/differential_forms/README.md) の余鎖複体と商ベクトル空間は、実装済みの加群上の構成を利用している。
この文書全体を一つの実装単位とし、各節は中間検査点とする。
一般のアーベル圏上の導来関手、導来圏、スペクトル系列は、この実装を用いて拡張する後続の単位とする。

## 現状

加群・複体の実装済み API は [algebra](../../libs/algebra/README.md) と [homological_algebra](../../libs/homological_algebra/README.md) にまとめる。

| 既存の実装 | 再利用する内容 | 本計画で追加する内容 |
| --- | --- | --- |
| `algebra.Module` | 加群準同型・同型、関数加群、部分加群、核・像・商と商の普遍性 | 第一同型定理、自由加群、直和、一般加群のテンソル積、射影加群 |
| `homological_algebra.Cochain`、`Integer` | 自然数・整数次数の余鎖複体、コホモロジー、誘導写像、零拡張と復元 | 鎖複体、鎖ホモトピー、シフト、cone、長完全列、分解と有限計算 |
| `algebra.Exact`、`Exact.Groups` | 核・像・完全性、可換群の核と像 | 短完全列、接続準同型、図式補題 |
| `linear_algebra.Field.Space` | 線形写像・部分空間・商・有限和・テンソル積 | 一般加群の構成との接続 |
| `std.Data.Nat.Gcd`、`Division` | 最大公約数と除法の数学的仕様・Program・対応証明 | 整数の拡張 Euclid、行列の整数基本変形、Smith 標準形 |
| `category` | 小圏、関手、自然変換、極限・随伴 | 加法圏・アーベル圏の語彙、加群族との接続 |

## 配置と依存

| パッケージ | 追加する module 群 |
| --- | --- |
| `std` | 整数の符号・整除・拡張 Euclid に必要な数値的補題、有限添字の演算 |
| `algebra` | `Module`、`Module.Hom`、`Submodule`、`Quotient`、`Free`、`DirectSum`、`Product`、`Tensor`、`Projective`、`IntegerMatrix`、`Smith` |
| `linear_algebra` | 一般加群構成の体上への具体化と既存 API との同型・整合性 |
| `category` | `Preadditive`、`Additive`、`Abelian` の構造と基本的な普遍性 |
| `homological_algebra` | `Chain`、`Cochain`、`Homology`、`Cohomology`、`Map`、`Homotopy`、`Cone`、`ExactSequence`、`Resolution`、`Ext`、`Tor`、`UniversalCoefficient`、`Kunneth`、`Finite` |

`homological_algebra` の直接依存は `std`・`algebra`・`category` とする。
一般の加群構成は `algebra` が所有し、体固有の構成と既存の利用側は `linear_algebra` が接続する。
この依存方向により `algebra` から `linear_algebra` への循環を生じさせず、整数係数と実数係数に同じホモロジーの構成を使える。
各パッケージは実際に直接 import する依存を `ref.toml` に宣言する。

## 1. 加群・自由加群・商

環と台集合を持つ加群の宣言の束を公開し、準同型の和・零・合成、同型と逆写像、部分加群、核・像・余核を構成する。
第一同型定理、部分加群の包含と商の対応、有限直和と積、短完全列の分裂補題を証明する。
整数倍を用いて可換群を整数加群にし、既存の `algebra.Exact.Groups` と接続する。

任意の集合 \(S\) 上の自由加群 \(R^{(S)}\) は、有限個の係数付き生成元の形式和から構成する。
加法・スカラー倍の関係で商を取り、有限支持関数による表示との同型を証明する。
自由加群からの準同型を生成元の像から一意に作れること、写像 \(S\to T\) に沿う押し出し、単射な生成元写像による部分加群を証明する。
任意集合の生成元と有限添字の実行可能な表現を分け、有限基底を受け取った場合に行列へ変換する。

加群の任意直和は有限支持族、任意積はすべての成分の族として構成する。
\(\operatorname{Hom}_R(R^{(S)},A)\cong A^S\) を公開する。
これが特異鎖の有限和と、特異余鎖の任意の値の割り当てを接続する API になる。

可換環上のテンソル積を双線形写像の普遍性で構成し、Hom–tensor の対応、右完全性、自由加群とのテンソル積を証明する。
商加群とテンソル積の体上への具体化を既存の線形代数に接続し、既存の普遍性と同じ写像を得ることを示す。

## 2. 複体・ホモロジー・ホモトピー

中核は整数次数とし、鎖複体は \(d_n:C_n\to C_{n-1}\)、余鎖複体は \(d^n:C^n\to C^{n+1}\) を持つ構造にする。
次数を反転する変換を提供し、両者の核・像・商を共通の構成で扱う。
非負次数の利用側には負次数を零加群で埋める構成を公開する。
De Rham 側の自然数次数 API には、この零拡張を通じて \(B^0=0\) の余鎖複体を与える。

サイクル・境界・ホモロジー、コサイクル・コバウンダリ・コホモロジーを加群として作る。
複体写像の誘導写像と恒等・合成の法則、ホモトピックな写像が同じ誘導写像を持つこと、鎖ホモトピー同値からホモロジー同型を得ることを証明する。
鎖ホモトピーは \(h_n:C_n\to D_{n+1}\)、\(f-g=dh+hd\) の規約に固定する。

シフト \((C[1])_n=C_{n-1}\) の微分は \(-d_C\) とする。
鎖写像 \(f:C\to D\) の cone は

\[
\operatorname{Cone}(f)_n=D_n\oplus C_{n-1},\qquad
d(y,x)=(d_Dy+f(x),-d_Cx)
\]

で構成し、二乗零、cone の短完全列、鎖写像がホモロジー同型を誘導することと cone のホモロジーが全次数で零になることの同値を証明する。
商複体と cone は比較写像を明示して接続する。

## 3. 完全列と接続写像

短完全列を写像と単射性・全射性・像と核の一致を持つ構造にする。
Snake lemma、Five lemma、短完全列の比較補題を加群の元と商の普遍性から証明する。
複体の短完全列から、代表元を持ち上げて微分し、核へ戻す操作により接続写像を構成する。
持ち上げの選択によらないこと、準同型性、各項での完全性、短完全列の射についての自然性を証明する。
鎖・余鎖の両方向の長完全列を公開する。

次数ごとに分裂した短完全列について、Hom による双対化の短完全性を証明する。
特異鎖の部分空間による列は、自由生成元の包含による分裂を使ってこの API に接続する。

## 4. 射影分解・Ext・Tor

射影加群は全射に対する持ち上げ性で定義する。
自由加群の射影性、直和・直和因子の射影性、加群の元を生成元とする自由加群からの全射を証明する。
核に自由加群からの全射を繰り返して、任意の加群に非負次数の自由分解を構成する。
次数ごとの台集合を組み立てる型値の定義と、その法則を別々に具体化できるようにする。

分解の比較定理と持ち上げの鎖ホモトピーまでの一意性、horseshoe lemma を証明する。
これにより、分解の選択を変えたときの同型とその整合性を持つ Ext・Tor を構成する。

\[
\operatorname{Ext}_R^n(M,N)=H^n(\operatorname{Hom}_R(P_\bullet,N)),\qquad
\operatorname{Tor}^R_n(M,N)=H_n(P_\bullet\otimes_R N).
\]

Ext の第1変数の反変性・第2変数の共変性、Tor の両変数の共変性、零次での Hom・tensor との同型、射影加群を第1引数とする高次の消滅を証明する。
短完全列に対応する Ext・Tor の長完全列と自然性を提供する。
非負二重複体の有限対角和による total 複体と比較を整え、両変数の射影分解を用いた Tor の計算が一致することを示す。
テンソル複体の微分には \(d(x\otimes y)=dx\otimes y+(-1)^{\deg x}x\otimes dy\) を用いる。

整数 \(m>0\) について、\(0\to\mathbb Z\xrightarrow{m}\mathbb Z\to\mathbb Z/m\to0\) を実際の自由分解にする。
これから \(\operatorname{Ext}^1_{\mathbb Z}(\mathbb Z/m,A)\cong A/mA\)、\(\operatorname{Tor}^{\mathbb Z}_1(\mathbb Z/m,A)\cong A[m]\) と高次の消滅を計算する。
\(\operatorname{Ext}^1\) と短完全拡大の同値類の対応も構成し、分裂拡大が零類になることを示す。

分解・導来関手の設計は [MIT Algebraic Topology I, Lectures 22–25](https://ocw.mit.edu/courses/18-905-algebraic-topology-i-fall-2016/pages/lecture-notes/) を照合先とする。

## 5. 普遍係数定理と Künneth

最初の計算用定理の入力は、有界で各項が有限自由な整数鎖複体とする。
有限自由整数加群の部分加群について、座標への射影の像が整数の主イデアルになることを用い、階数に関する帰納法で有限生成性を証明する。
得られた生成行列の Smith 標準形から自由基底を構成し、サイクル・境界の分裂を用いて以下を構成する。

\[
0\longrightarrow\operatorname{Ext}^1_{\mathbb Z}(H_{n-1}(C),A)
\longrightarrow H^n(\operatorname{Hom}_{\mathbb Z}(C,A))
\longrightarrow\operatorname{Hom}_{\mathbb Z}(H_n(C),A)
\longrightarrow0,
\]

\[
0\longrightarrow H_n(C)\otimes A
\longrightarrow H_n(C\otimes A)
\longrightarrow\operatorname{Tor}^{\mathbb Z}_1(H_{n-1}(C),A)
\longrightarrow0.
\]

自然な短完全列と、基底や分裂の選択を含む直和同型を別の構造として公開する。
有界有限自由複体 \(C,D\) についても、テンソル積のホモロジーへの外積と Tor 項を持つ Künneth 短完全列を証明する。
体上では有限自由複体のコホモロジーのテンソル積が積複体のコホモロジーになることを示す。
この有限性は定理の型に記録する。
任意の特異鎖複体への一般化には無限ランク自由加群の部分加群に関する理論を追加する後続の段階を設け、今回の位相的計算には有限モデルとの比較を用いる。

普遍係数・Künneth の仮定、完全列、分裂の扱いは [Weibel, Chapter 3, §3.6](https://math.mit.edu/~hrm/palestine/weibel/03-tor_and_ext.pdf) と照合する。

## 6. 有限複体の実行可能な計算

有限自由複体を各次数の基底と整数境界行列で表示する。
拡張 Euclid と行・列の基本変形から Smith 標準形を計算し、変換行列とその逆、対角成分の非負性・整除列、\(UAV=D\) の証明を返す。
停止性は Euclid の剰余の減少と、確定済みの行・列数で証明する。
実行部を `\machine`、数学的仕様との対応を `\correspondence` と既存の Program の証明で接続する。

ホモロジー計算では、\(d_n\) の Smith 標準形で得た核の基底へ \(d_{n+1}\) を変換し、その核内の像の行列をさらに標準化する。
この過程で基底変更を隣接行列に伝播させ、\(d_nd_{n+1}=0\) の証明を保持する。
余鎖の微分は境界行列の転置として構成し、同じ処理でコホモロジーを計算する。

返却するデータは自由階数、巡回因子、元の複体における生成元、商との双方向の写像と逆の法則である。
有限複体間の写像を入力すると、これらの生成元での誘導写像を計算できるようにする。
有限行列の証明付き計算に必要な時間とメモリを代表例で測定し、数学的な仕様と実行の対応を保って改善する。

## 7. 圏論との接続

`category` に前加法圏・零対象・二項双積・核・余核・アーベル圏の条件を追加する。
抽象圏の構造について、射の加法と合成、核と余核の一意性、双積の行列計算を証明する。
既存の `Category.Object` は集合なので、加群の圏を利用する際は集合で添字付けられた加群族と、その間の全準同型を射とする圏を構成する。
アーベル圏として具体化するときは、この族が必要な零対象・双積・核・余核を備えるデータと法則を渡す。
対象族を変える場合の表現は、宣言の束を用いた一般加群の定理側で扱う。
ホモロジーの関手性と完全列の自然性を、対応する族上の関手・自然変換として接続する。

## 実装順・検査・完了条件

実装順は第1節、第2節、第3節、第4節、第6節、第5節、第7節とする。
第5節が用いる有限自由加群の部分加群の構成は第6節で揃える。
De Rham 側は第1・2節の API から利用できるが、本計画の完了判定には全節を含める。

`tests/projects/homological-algebra` に以下の証明付き利用例を置く。

| 例 | 完了時に示すこと |
| --- | --- |
| 一つの次数に集中した加群、零複体、恒等写像の cone | ホモロジーの定義、シフトと端の次数、収縮の符号 |
| \(\mathbb Z\xrightarrow{m}\mathbb Z\)、\(m>0\) | ホモロジー・余核、双対余鎖の次数、Ext・Tor の計算 |
| \(\mathbb Z/2\) と \(\mathbb Z/4\) | \(\operatorname{Ext}^1\)・\(\operatorname{Tor}_1\) がともに \(\mathbb Z/2\) になる計算と係数写像 |
| 短完全列の可換図式 | 接続写像の自然性、完全性、比較定理の利用 |
| 非対角整数境界行列を持つ三項複体 | 核内での像の計算、隣接行列の基底変更、誘導写像 |
| 有限自由複体のテンソル積 | Künneth の Tor 項と体係数での消滅 |
| 体上の余鎖複体 | `linear_algebra` の構造と共通の商・コホモロジーの接続 |

```sh
cargo build -p cli
for package in std algebra category linear_algebra homological_algebra; do
  target/debug/cli "libs/$package" --module "$package" --no-cache --diagnostics compact || exit 1
done
target/debug/cli tests/projects/homological-algebra --module homological_algebra_tests --no-cache --diagnostics compact
target/debug/cli tests/projects/library --module library_tests --no-cache --diagnostics compact
target/debug/cli tests/projects/category --module category_tests --no-cache --diagnostics compact
target/debug/cli tests/projects/topological-k-theory --module topological_k_theory_foundations_tests --no-cache --diagnostics compact
cargo test -p cli --test ref_files --locked
```

新しい project を `src/cli/tests/ref_files.rs` に登録し、公開 module、各 README、`libs/README.md` の依存と検査手順を更新する。
前提は定理の命題全体に量化し、具体的な複体や分解を構成した後で一般定理へ渡す。
集合族、商、型値の帰納的構成は小さな別 module から先に利用して型の受け渡しを検査する。
言語・体系の制限で構成できないと判明した場合は、書きたい形・最小例・診断・影響範囲を [gaps.md](../gaps.md) に記録して停止する。
