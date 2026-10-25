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

`algebra.Polynomial.Over.Finite` は任意の可換環上の有限係数表示・演算・padding を公開する。
既存の体上の `galois` の係数演算と `polynomial_linear_algebra.Field.Representatives.exists` もこの実装を共用する。
K04 の `Circle.Coefficients.valueContinuous` を公開し、評価の連続性を利用する。

## 検証と引き継ぎ

ブランチは `math/k07-clutching-linearization`、開始点は main `744d501e`。
#42〜#45 の統合と重複 PR の不在を確認して開始した。
K07 は [draft PR #46](https://github.com/pdf-jube-joba/ref-type/pull/46) で進行中であり、未マージ。
K02・B09・K03 は未着手。

| 対象 | 数学入力コミット | 結果 |
| --- | --- | --- |
| K07 全対象（当時の実装範囲） | `67f32242` | accepted・保存完了・終了0 |
| B04 cocycle 等式比較 | `b3f782ef` | accepted・保存失敗0・終了0 |
| 座標の連続性 | `d2a50e80` | accepted・保存完了・終了0 |
| ShiftFamilies | `b2901d44` | accepted・保存完了・終了0 |
| Companion.Families.Linearization | `19b1962e` | accepted・保存失敗0・終了0 |
| PolynomialEigen | `8502642e` | accepted・保存完了・終了0 |
| SpectralPencil | `11f6a15c` | accepted・保存失敗0・終了0 |
| SpectralMotion | `1208fe83` | accepted・保存失敗0・終了0 |

検査は source snapshot と共有キャッシュを使用した。
最後に成功した個別対象は SpectralMotion で、連続な族・全時刻の可逆性・両端の等式を含む。
その後の NormalForm、InverseFamily、Endpoint、ClutchedMotion、Normal/Clutched、companion の円周上 gauge 比較、dimensionFormula は未検証。
既存の多項式係数 API 共通化の影響先 polynomial_linear_algebra.Field.Representatives の個別検査は終了0。
Rust の変更はない。

2026-10-25、実行ツールが `exec-server transport disconnected` で切断された。
状態 API は running / connected・failure=null を返したが、再確認した exec_command と write_stdin は `No usable execution environment is available. Wait for an environment to become available before using this tool.` と拒否された。
保持された診断記録は history_status=not_found・records=[] で、原因は不明。
設定・プロキシ・認証情報の変更は行っていない。
GitHub 連携は正常に PR 情報を取得でき、退避にも使用した。

切断時の検査は `work/k07-clutching-comparison-current`、入力コミット `74c41afd`、対象 `clutching_linearization.Linearization.On.Matrices.Clutched`。
最後の観測は checking (541s)、Along module まで到達したが、終了コード・最終結果・キャッシュ保存は確認できず検証未完了。
以前の検査では非公開 alias、名前衝突、連続性証明の型推論エラーを修正した。
タイムアウト（終了2）と中断（終了130）は成功扱いしていない。

切断前に git push と ls-remote で確認した最終 SHA は `7ac02faf8022f09a9fc82e409a4938715cd0e760`。
この退避コミットは、その子として Normal/Clutched と親 module 宣言、および本引き継ぎを GitHub 連携経由で保存する。
Normal/Clutched の初版の parse-only は終了0だったが、identity 証明修正後は再実行できていないため未検証。
秘密情報・生成キャッシュ・ログは含めていない。

再開時は remote branch とローカル差分を比較して引き継ぎ、上書きや重複 PR を避ける。
環境が新規なら当該 branch を取得して `cargo build -p cli --locked`（切断前は終了0）から再開する。
残存する work のレポートがあれば正常終了を確認し、終了不明なら再検査する。

```sh
target/debug/cli libs/topology/clutching_linearization --parse-only --save-source-snapshot work/k07-resume.source.json
target/debug/cli libs/topology/clutching_linearization --source-snapshot work/k07-resume.source.json --module clutching_linearization.Linearization.On.Matrices.Clutched --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 900 --report-json work/k07-resume.report.json
```

次に追加した NormalForm・InverseFamily・SpectralMotion.Normal・ClutchedMotion と companion gauge の対象検査を行う。
clutching とスペクトル束の比較、選択独立性・自然性・直和・相互逆、具体例、workspace/package 登録・公開一覧・下流リンク・ロードマップが残作業。
package 全依存閉包・影響する下流・利用例・workspace の最終検証も残っている。
K07 の完成・最終検証・必要な CI・通常マージ・main 反映確認までが、この再開作業の対象。

2026-10-25、新しい実行環境で退避 head `060c0616a1c3f648a967fd40897a35706c60ffcb` を取得し、GitHub と git ls-remote の一致を確認した。
旧環境の work レポートと libs/refcache は残っていないため、共有キャッシュを再構築して Clutched から検査を再開する。
数学ソースの検証状態は上記のままであり、この再開記録は検証成功を示すものではない。

再開後、Laurent 近似のホモトピーを実際の束同型へ接続する `On.Matrices.Result.Clutching.isomorphismExists` を追加した（未検証）。
処理系のビルドと退避時ソースの parse-only は終了0。
Clutched の型検査は `/tmp/k07-resume/source.json` を入力に `libs/refcache` で実行中であり、最終結果はまだ未確認。

さらに `SpectralMotion.Comparison`、`Companion.Families.Linearization.Gauges.SpectralForm` と `Separated.Bundles.Deformation` を追加し、pencil の二つの表示と射影の標準形への束比較を接続した。
行列族の等式からの束同型 `Clutched.Comparison.ofEquality` も公開した。
これらは parse-only 終了0、型検査は未完了であり WIP として保存する。

`Construction.Clutching.spectralComparisonExists` へ標準形比較を公開し、`Examples.Empty` と `Examples.Nilpotent` の利用例を追加した（型検査待ち）。

Clutched の再検査は `Along.isomorphismExists` で長時間停滞し、計測のため中断した（終了130）。
最初のレポートは 11,896 source steps、checkpoint 11,468、保存失敗0であり、成功ではない。
宣言計測では `startExists`・`finishExists` までは完了したため、最終合成を `motionExists`・`throughInitialExists` に分けて検査箇所を絞る（未検証）。

計測により `motionExists` は完了し、`throughInitialExists` から参照される `startExists` の kernel 登録時の型同値判定で展開が増大していると分かった。
比較回数と項を限定出力する `REF_TYPE_PROFILE_CONVERSION` の診断を追加した。判定規則は変更していない。
