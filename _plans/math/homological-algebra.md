# ホモロジー代数の比較・自然性・Künneth

## 到達点と配置

有限自由整数複体の普遍係数定理を自然な短完全列として公開し、整数係数の Künneth 短完全列と体係数の標準外積同型を整える。
[特異コホモロジー計画](singular-cohomology.md) の有限モデルへ、群・積・誘導写像の証明付き計算を渡すことを到達点とする。
本計画全体を一つの実装単位とし、各節を中間検査点とする。

既存 API の一覧は [ライブラリ一覧](../../libs/README.md) と各パッケージの README を参照する。
追加する構成は現在の分割に合わせて配置する。

| 配置・パッケージ | 追加する内容 |
| --- | --- |
| [algebra/homological/resolutions](../../libs/algebra/homological/resolutions/README.md)・`resolutions` | 二つの射影分解のテンソル total と片側の分解との比較写像、ホモロジー同型の証明 |
| [algebra/homological/derived_functors](../../libs/algebra/homological/derived_functors/README.md)・`derived_functors` | Tor の両変数での計算の一致、普遍係数短完全列の抽象化と自然性 |
| [algebra/homological/computations](../../libs/algebra/homological/computations/README.md)・`homological_algebra` | 有限モデルとの接続、整数 Künneth、体係数の外積と同型の比較 |

加群の構成は `module_theory`・`commutative_algebra`、一般複体は `chain_complexes`、Smith 計算と部分加群の基底は `integer_matrices`・`finitely_generated_modules` を使う。
配置名 `computations` と import 名 `homological_algebra` を区別し、各 `ref.toml` には直接 import する依存を宣言する。
パッケージ分割は `std` 以外で約5,000行を目安に、共有基盤から応用へ依存する単位で行う。

## 1. 両側の分解による Tor の比較

`resolutions.DoubleComplex` と `ResolutionTensor` を使い、両変数の射影分解から作るテンソル二重複体の total を構成する。
各増大写像から、一方だけを分解したテンソル複体への比較写像を作り、ホモロジー同型を誘導することを証明する。
`derived_functors.Tor` に、両変数のどちらを分解しても得られる計算が一致する同型を公開する。
分解変更、係数写像、変数交換、長完全列の接続写像との整合性を示す。

テンソル鎖複体の符号は

\[
d(x\otimes y)=dx\otimes y+(-1)^{\deg x}x\otimes dy
\]

にそろえ、非負次数から整数次数への零拡張と両立させる。
照合先は [MIT Algebraic Topology I, Lectures 22–25](https://ocw.mit.edu/courses/18-905-algebraic-topology-i-fall-2016/pages/lecture-notes/) とする。

## 2. 普遍係数短完全列の自然性

`Finite.Bounded.Of.At.UniversalCoefficient.CohomologyKernel.sequence` と `Tensor.Projection.Exactness.Derived.sequence` を起点に、短完全列全体の自然性を証明する。
複体写像と係数写像について Ext¹ 側の包含・Tor₁ 側の射影まで可換図式を構成し、恒等写像と合成の法則を公開する。
評価写像の可換性には `derived_functors.UniversalCoefficient.Over.Morphism.On.At.naturality` を使う。

サイクルと境界の射影性を条件とする共通の証明を `derived_functors` に切り出し、有限自由整数複体への具体化を `homological_algebra` に置く。
境界・サイクルの分解や基底を変更した際に、Ext・Tor の分解変更同型を介して短完全列の写像が一致することを証明する。
Smith 計算による分裂との関係は、選択を含む直和表示と標準の短完全列の対応として示す。

`Finite.Bounded.Mapping` の計算した生成元に自然性の図式を移し、非対角の境界行列と基底変更を含む例を追加する。
照合先は [Weibel, Chapter 3, §3.6](https://math.mit.edu/~hrm/palestine/weibel/03-tor_and_ext.pdf) とする。

## 3. 整数係数の Künneth

有界有限自由整数鎖複体 \(C,D\) に対して、外積を左の写像とする短完全列を証明する。

\[
0\longrightarrow\bigoplus_{p+q=n}H_p(C)\otimes H_q(D)
\longrightarrow H_n(C\otimes D)
\longrightarrow\bigoplus_{p+q=n-1}\operatorname{Tor}^{\mathbb Z}_1(H_p(C),H_q(D))
\longrightarrow0.
\]

有限自由整数加群の部分加群の基底と第1節の比較を使い、両因子の写像についての自然性と、選んだ分裂による直和表示を証明する。
整数次数のテンソル total、外積、有限行列計算への接続を `homological_algebra.Kunneth` に置く。
Smith 計算で得る生成元上の写像と、抽象的な外積・Tor 項の写像が一致することを示す。

## 4. 体係数の標準外積同型

`Kunneth.Field.Of.With.At.isomorphism` の逆が `TensorCochain.Exterior.map` から得る外積と一致することを証明する。
各 \(p+q=n\) の外積を有限対角直和の普遍性でまとめ、分裂の選択によらない標準の Künneth 同型を公開する。
`TensorCochain.CycleProductNaturality` と `Swap` を使い、両因子の写像についての自然性、交換の \((-1)^{pq}\) の符号、単位との整合性を示す。

整数係数・体係数とも有限性を定理の入力型に保持する。
特異理論への適用は有限モデルとの証明済みの比較を通じて行い、無限ランクの場合の一般化は後続の実装単位とする。
一般のアーベル圏上の導来関手、導来圏、スペクトル系列も後続の単位とする。

## 利用例・検査・完了条件

[libs/algebra/homological/concrete_complexes](../../libs/algebra/homological/concrete_complexes/README.md) に、追加した写像とその可換図式を利用する例を置く。

| 利用例 | 追加する確認 |
| --- | --- |
| `Cyclic`・`ExactSequences` | Tor の両側の計算、分解変更と接続写像の整合性 |
| `Finite.Bounded.UniversalCoefficient` | 複体・係数写像による短完全列全体の自然性、基底変更との可換性 |
| `Field.Tensor` | 外積と Künneth 同型の一致、分裂変更、交換の符号と単位 |
| 整数複体のテンソル積 | 非零の Tor 項、短完全列の自然性、選択を含む分裂と生成元の計算 |

第1節から第4節まで順に進め、定理は対象と仮定を命題内で量化して公開する。
検査は [CLI のキャッシュと範囲選択](../../src/USAGE.md) に従い、変更した module と利用 project を指定する。
ライブラリの検査は workspace の `libs/refcache/` を共有する。

```sh
cargo build -p cli
cargo run -p cli -- libs/algebra/homological/resolutions --module resolutions
cargo run -p cli -- libs/algebra/homological/derived_functors --module derived_functors
cargo run -p cli -- libs/algebra/homological/computations --module homological_algebra
cargo run -p cli -- libs/algebra/homological/concrete_complexes --module concrete_complexes
cargo run -p cli -- libs/std
cargo run -p cli -- libs/geometry/coordinate_calculus
```

完了条件は Tor の両側の比較、普遍係数短完全列全体の自然性、整数 Künneth、体係数の標準外積同型とその自然性・符号・単位、計算例がそろうことである。
公開 module、各 README、`libs/README.md` を更新し、分割で新規パッケージを設けた場合は `libs/ref.toml` の `[workspace].packages` に追加する。
具体的な複体の構成と証明は `libs/algebra/homological/concrete_complexes/` に置き、`libs/ref.toml` の workspace から検査する。
言語・体系の制限に直面した場合は、書きたい形と現在の書き方を100行以内の playground 用の再現例として [gaps.md](../gaps.md) に記録する。
回避する構成も成立しない致命的な制限と判明した場合は、診断と影響範囲を明記して停止する。
