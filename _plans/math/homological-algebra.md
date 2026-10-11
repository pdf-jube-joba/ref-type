# ホモロジー代数の基盤と有限複体の計算

## 到達点と現在の位置

可換環上の加群・複体・射影分解を基礎に、有限自由整数複体のホモロジー・コホモロジーと誘導写像を証明付きで計算する。
普遍係数定理と整数係数の Künneth 短完全列を整え、[特異コホモロジー計画](singular-cohomology.md) の有限モデルに適用できる状態を到達点とする。

基礎構成と有限行列計算は既に複数のパッケージへ実装されている。
この計画は、それらを再利用して残る比較定理・完全列・自然性を仕上げる一つの実装単位である。
各節は中間検査点とし、一般のアーベル圏上の導来関手、導来圏、スペクトル系列は後続の実装単位とする。
[De Rham コホモロジー](../../libs/geometry/differential_forms/README.md) は `module_theory` と `chain_complexes` の共通構成を利用している。

## 実装済みの基盤と所有するパッケージ

配置は各パッケージの `ref.toml` と `src/root.ref` を基準にする。

| パッケージ | 再利用する公開 API と証明 |
| --- | --- |
| [std](../../libs/std/README.md) | 整数・自然数、除法、拡張 Euclid、有限添字、証明付き Program。 |
| [algebra](../../libs/algebra/basic/README.md) | 準同型、群完成、群・環の商、多項式、`Exact` の完全性。 |
| [module_theory](../../libs/algebra/module_theory/README.md) | `Module.Over` の加群、核・像・商、第一同型定理、自由加群と有限支持表示、任意直和・積、テンソル積、射影性、短完全列、Snake・Five lemma、自由分解の各項。 |
| [commutative_algebra](../../libs/algebra/commutative_algebra/README.md) | `Modules` の Hom 加群、自由加群からの Hom、Hom–tensor 対応、射影加群とのテンソルによる短完全列の保存、行列と準同型の往復。 |
| [integer_matrices](../../libs/algebra/integer_matrices/README.md) | 整数行列の実行可能な演算、Smith 標準形、変換行列と逆、停止性、\(UAV=D\)、非負対角成分と整除列。 |
| [finitely_generated_modules](../../libs/algebra/finitely_generated_modules/README.md) | 整数行列の核・像の自由基底、有限自由整数加群の部分加群の有限生成性と自由基底、体上の部分空間の射影性。 |
| [chain_complexes](../../libs/algebra/homological/chain_complexes/README.md) | 自然数・整数次数の余鎖複体、整数次数の鎖複体、零拡張、次数反転、誘導写像、ホモトピー、シフト、cone と非輪状性の判定、長完全列と接続写像の自然性。 |
| [resolutions](../../libs/algebra/homological/resolutions/README.md) | 非負鎖複体、射影分解、比較定理とホモトピーによる一意性、horseshoe、Hom・テンソル複体、二重複体と有限対角和の total。 |
| [derived_functors](../../libs/algebra/homological/derived_functors/README.md) | Ext・Tor、分解の変更、零次の Hom・tensor 同型、射影加群の高次消滅、両変数の短完全列、巡回加群の計算、Ext¹ と短完全拡大の対応、普遍係数の評価写像。 |
| [homological_algebra](../../libs/algebra/homological/computations/README.md) | `Finite` の二段階 Smith 計算、有界整数複体と転置した余鎖複体、基底変更と誘導写像、`FieldFinite` の分裂、`TensorCochain` の total・交換・外積と自然性、`Kunneth.Field` の同型。 |
| [category](../../libs/category/README.md) | 前加法圏、双積、核・余核とアーベル圏の構造。 |
| [linear_algebra](../../libs/algebra/linear_algebra/README.md) | 体上への具体化、一般加群のテンソル積との比較。 |

`homological_algebra` の現在の直接依存は `algebra`、`chain_complexes`、`commutative_algebra`、`derived_functors`、`finitely_generated_modules`、`integer_matrices`、`module_theory`、`resolutions`、`std` である。
一般の複体は `chain_complexes`、分解は `resolutions`、Ext・Tor は `derived_functors` が所有し、有限計算と積の比較を `homological_algebra` に置く。
各パッケージは直接 import する依存を宣言し、`std` 以外は約5,000行を目安に共有基盤から応用へ分ける。

## 1. 分解と Tor の比較

既存の比較定理・horseshoe・分解変更の同型を用いて、両変数の射影分解から作る二重複体の total と、一方だけを分解したテンソル複体との比較を構成する。
増大写像から得る比較写像がホモロジー同型を誘導することを証明し、Tor の両変数での計算の一致、分解変更・係数写像・変数交換との整合性を公開する。
二重複体と比較写像は `resolutions`、Tor としての同型と自然性は `derived_functors` に置く。

テンソル鎖複体の符号は

\[
d(x\otimes y)=dx\otimes y+(-1)^{\deg x}x\otimes dy
\]

にそろえ、非負次数から整数次数への零拡張と両立させる。
既存の Ext・Tor の長完全列について、この比較の下で接続写像が一致することを示す。
分解・導来関手の照合先は [MIT Algebraic Topology I, Lectures 22–25](https://ocw.mit.edu/courses/18-905-algebraic-topology-i-fall-2016/pages/lecture-notes/) とする。

## 2. 有限自由整数複体の普遍係数定理

`derived_functors.UniversalCoefficient.Over.On.At.map` は
\(H^n(\operatorname{Hom}_R(C,A))\to\operatorname{Hom}_R(H_n(C),A)\)
を構成し、`Morphism` はその自然性を扱う。
ここから、有界で各項が有限自由な整数鎖複体に対して、核の同定・全射性・接続写像を追加する。

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

`finitely_generated_modules.IntegerSubmodules` の自由基底を使い、サイクルと境界の短完全列を分裂させる。
自然な短完全列を `derived_functors` に、有限行列表現から仮定を具体化する接続を `homological_algebra` に置く。
基底や切断を選んで得る直和同型と、選択によらない短完全列を別の構造として公開する。
複体写像と係数写像についての自然性、零次と負次数の端、巡回因子に対する Ext・Tor の計算まで接続する。

## 3. 整数係数の Künneth と体係数の外積

有界有限自由整数鎖複体 \(C,D\) に対して、外積を左の写像とする短完全列を証明する。

\[
0\longrightarrow\bigoplus_{p+q=n}H_p(C)\otimes H_q(D)
\longrightarrow H_n(C\otimes D)
\longrightarrow\bigoplus_{p+q=n-1}\operatorname{Tor}^{\mathbb Z}_1(H_p(C),H_q(D))
\longrightarrow0.
\]

有限自由整数加群の部分加群の基底と第1節の Tor 比較を使い、両因子の写像に対する自然性と、選んだ分裂による直和表示を証明する。
定理と有限モデルへの接続は `homological_algebra.Kunneth` に置く。

`Kunneth.Field.Of.With.At.isomorphism` は、体上の有界有限自由余鎖複体について、選んだ分裂から total のコホモロジーとコホモロジー族のテンソル total の同型を返す。
`TensorCochain.Exterior.map` はサイクル代表元から定めた外積であり、その自然性も実装されている。
この外積が既存の分裂同型の逆と一致することを示し、分裂の選択によらない標準の Künneth 同型、交換の \((-1)^{pq}\) の符号、単位との整合性を公開する。

有限性は定理の入力型に保持する。
任意の特異鎖複体に適用する段階では、有限モデルとの証明済みの比較を使う。
無限ランク自由加群の部分加群の理論は後続の一般化として扱う。
普遍係数と Künneth の仮定・完全列・分裂は [Weibel, Chapter 3, §3.6](https://math.mit.edu/~hrm/palestine/weibel/03-tor_and_ext.pdf) と照合する。

## 4. 既存の計算と利用例への接続

`Finite.Pair.Of.Result` と `Finite.Bounded.Of.At.Result` が返す、元のサイクルの商と巡回加群の積との同型を使う。
基底変更、転置による余鎖、計算した生成元上の誘導写像まで既存の `Finite.Bounded` と `Mapping` に接続済みである。
新しい普遍係数・Künneth の写像をこの同型へ移し、抽象的な定理の結果と実行可能な行列計算が一致することを証明する。

[既存の利用例](../../tests/projects/homological-algebra/README.md) を拡充する。

| 利用例 | 追加する確認 |
| --- | --- |
| `BasicComplexes`、`Chains` | 零複体、単一次数、cone、シフトと新しい完全列の端の次数。 |
| `Cyclic`、`Cyclic.Extensions` | \(\mathbb Z/2\)・\(\mathbb Z/4\) の既存計算と Tor 比較・普遍係数の写像の一致。 |
| `ExactSequences` | 複体・係数の可換図式と接続写像の自然性。 |
| `Finite`、`Finite.Bounded` | 非対角境界行列、基底変更、計算した生成元での普遍係数写像。 |
| `Field.Tensor` | 外積が Künneth 同型を与えること、交換の符号と写像との可換性。 |
| 整数複体のテンソル積 | 非零の Tor 項を持つ短完全列と選択を含む分裂。 |

## 実装順・検査・完了条件

第1節、第2節、第3節、第4節の順に実装する。
加群、Smith 計算、複体、分解、Ext¹ の拡大表示は既存 API を利用する。
定理は対象と仮定を命題内で量化し、具体的な複体・分解・基底を構成した後で適用する。

検査手順は [libs の型検査](../../libs/README.md#型検査) に合わせる。

```sh
cargo build -p cli
cargo run -p cli -- --full-check libs
cargo run -p cli -- --full-check tests/projects/homological-algebra
cargo run -p cli -- tests/projects/library
cargo run -p cli -- tests/projects/category
cargo run -p cli -- tests/projects/manifolds-de-rham
cargo run -p cli -- tests/projects/topological-k-theory
cargo test -p cli --test ref_files --locked
```

完了条件は Tor の比較、二つの普遍係数短完全列、整数 Künneth 短完全列、体係数の標準外積同型、それらの自然性と計算例がそろうことである。
公開 module、各 README、`libs/README.md` を更新し、新規利用 project が必要なら `src/cli/tests/ref_files.rs` に登録する。
言語・体系の制限で構成できないと判明した場合は、書きたい形・100行以内の最小例・現在の書き方・診断・影響範囲を [gaps.md](../gaps.md) に記録し、その理由を明記して停止する。
