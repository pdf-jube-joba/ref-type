# clutching の安定線形化（K07、実装中）

入口は `clutching_linearization.Linearization`。
K04 の Laurent 近似、K06 のスペクトル分離、K01 の束の同型類と K0 を再利用する。

| API | 構成・証明 |
| --- | --- |
| `Blocks` | 上下の剪断写像、両逆、Schur 補元の分解、可逆な経路 |
| `Uniform` / `MatrixNeighborhoods.Perturbation` | 行列の開近傍の共通誤差幅、コンパクト底上での可逆性の余裕 |
| `On.Matrices.exists` / `Result` | 連続可逆行列族の Laurent 近似、可逆なホモトピー、両端の等式、連続な逆行列と両逆 |
| `LaurentNormal.exists` / `finiteExists` | 負の冪を払った多項式と有限係数表示 |
| `LaurentNormal.Matrices.commonExists` / `finiteMatrixExists` | 全成分に共通の shift・次数・有限係数配列 |
| `Coordinates.At.frame` / `Families` | 有限個の座標ブロックの比較同型と族の連続性 |
| `Companion.With.Eigen` | 固有ベクトルから多項式の核への写像、単位円固有値の不在の判定 |
| `Companion.Families.Separated` / `KClass` | 連続な companion 行列、スペクトル像束とその K0 の差の定義 |
| `On.SpectralIndex.Pullback.naturality` / `Sum.Difference.additivity` | スペクトル束の差の引き戻し自然性と直和加法性 |
| `On.SpectralHomotopy.invariant` | 単位円との分離を保つ行列族の両端の K0 の差の一致 |
| `On.Matrices.Clutched.Scaling` / `Normalized.With.Shifted.Leading.Clutching` | 定数倍・正規化時の摂動による clutching 束比較 |
| `On.Matrices.Construction.Clutching.shiftedComparisonExists` | 自明束を加えた shifted loop からスペクトル標準形への比較（検証済み） |

`algebra.Polynomial.Over.Finite` は任意の可換環上の有限係数表示・演算・padding を公開する。
既存の体上の `galois` の係数演算と `polynomial_linear_algebra.Field.Representatives.exists` もこの実装を共用する。
K04 の `Circle.Coefficients.valueContinuous` を公開し、評価の連続性を利用する。

## 検証と引き継ぎ

作業は `math/k07-clutching-linearization` / [draft PR #46](https://github.com/pdf-jube-joba/ref-type/pull/46)、基点は main `744d501e`。
新環境で退避 head `060c0616` を取得し、旧 work・キャッシュがない状態から共有キャッシュを再構築した。

| 対象 | 数学入力 | 結果 |
| --- | --- | --- |
| Clutched（ホモトピー・gauge 比較） | `cdbdc077` | accepted・保存失敗0・終了0、895 module |
| K07 全対象（現在の実装範囲） | `e19631fb` | accepted・保存失敗0・終了0、1,221 module |
| kernel 既存テスト | `874e6292` の処理系 | 78 passed、終了0 |

K07 全対象は `/tmp/k07-resume/target-2.json`、約47秒、1,301 source steps、最大RSS 2,283,812 KiB。
復旧・重複・再実行・lost steps は各0で、プロセス終了と最終保存を確認した。
NormalForm・InverseFamily・ClutchedMotion・Normal/Clutched・companion gauge 比較、および再開後の追加を含む。
処理系には比較回数を限定表示する `REF_TYPE_PROFILE_CONVERSION` の診断だけを追加し、型判定規則は変更していない。

再開後の主な接続:

- `On.Matrices.Result.Clutching.isomorphismExists`: 元のループと Laurent 近似の clutching 束の同型。
- `SpectralMotion.Comparison.isomorphismExists`: spectral pencil と射影の標準ループの clutching 束の同型。
- `Companion.Families.Linearization.Gauges.SpectralForm`: ブロック行列と spectral pencil の等式。
- `Construction.Clutching.spectralComparisonExists`: 安定対角形からスペクトル標準形への束比較。
- `Examples.Empty`・`Examples.Nilpotent`: 零次元と2次の冪零行列で比較を利用する具体例。

以前の Clutched 検査は `Along` 内の型同値判定で停滞し、診断のため中断した（終了130、成功ではない）。
B04 `Clutching.Homotopy.Endpoint.at` を実際に束構成が使う `Pullback.pulledG` の別名に整理すると、巨大な束の型展開を避け、Along は約0.7秒で完了した。
`IsomorphismComposition.Isomorphism` の公開と型付きの中間証明も追加した。

検査コマンド:

```sh
source /workspace/ref-type-env.sh
cargo build -p cli --locked
target/debug/cli libs/topology/clutching_linearization --parse-only --save-source-snapshot /tmp/k07-resume/current.source.json
REF_TYPE_PROFILE_PROGRESS=1 target/debug/cli libs/topology/clutching_linearization --source-snapshot /tmp/k07-resume/current.source.json --module clutching_linearization --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 1800 --report-json /tmp/k07-resume/target.json
```

`On.SpectralIndex` にスペクトル束の差を共通化し、`On.SpectralHomotopy.invariant` にスペクトル分離を保つ変形の両端の差の等式を追加した。
`5bc767f4` の K07 全対象は `/tmp/k07-resume/index.json` で accepted・保存失敗0・終了0。
`8202b036` の `SpectralIndex.Pullback.naturality` と引き戻した自明束の比較も、`/tmp/k07-resume/pullback.json` で accepted・保存失敗0・終了0。
`SpectralSum.off` と `SpectralSum.Projection.formula` は `/tmp/k07-resume/sum.json` で accepted・保存失敗0・終了0。
`6e52e50c` の K07 全対象は `/tmp/k07-resume/normalization.json` で accepted・保存失敗0・終了0（1,287 module、約50秒）。
`SpectralIndex.Sum.BundlesComparison.isomorphism` と `Sum.Difference.additivity` に直和の束同型・K0 の加法性を追加し、`TrivialSum` の自明束の比較も利用して証明した。
`Clutched.Scaling.isomorphism` と `Normalized.With.Shifted.Leading.Clutching.isomorphismExists` に、摂動と非零定数倍による正規化の束比較を追加した。
`Matrices.ApproximationComparison.isomorphismExists` は Laurent 近似の選択によらない clutching 束同型。
`a4ead646` の package 全依存閉包は `/tmp/k07-resume/closure.json` で accepted・保存失敗0・終了0（5,638 module、約26分、復旧・重複・lost steps すべて0）。
`f9f665b2` の最新 K07 全対象は `/tmp/k07-resume/stabilization-3.json` で accepted・保存失敗0・終了0（1,300 module）。
`Construction.Clutching.stabilizedComparisonExists` と `shiftedComparisonExists` は monic および shifted loop に自明束を加えた束からスペクトル標準形への同型を与える。
Rust workspace は383 tests passed・終了0、format と Clippy（全workspace・全targets・警告をエラー化）も終了0。
次は workspace 全体で影響先を検査する。これらはまだ元の clutching の安定化から K0 の差への完全な変換・相互逆を意味しない。

残る数学的な接続は、Laurent shift による円周の冪を K0 の自明束の差へ反映すること、射影の標準ループの clutching と像束の差を同定すること、任意の shift・次数・正規化パラメータについての選択独立性、および基本積定理に必要な相互逆の等式。
現在のスペクトル族の自然性・直和・ホモトピー不変性と、近似間の clutching 束同型だけからは、これらの結論はまだ出せない。
workspace・公開一覧・下流リンク・ロードマップには実装中の状態を反映した。
package 全依存閉包の検査後に、最新追加と影響先の検査を行う。
その後に PR の差分・必要な CI を確認して ready にし、通常マージと main 反映を確認する。
