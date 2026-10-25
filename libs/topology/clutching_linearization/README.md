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
GitHub 連携で #42〜#45 の統合を確認済み、開始時の open PR 検索結果は空であった。
通常の GitHub 連携は PR 情報の読み取りに成功し、gh / curl 経由で観測した拒否とは区別する。
K07 の PR はまだ作成していない。

最後に対象検査が成功した数学ソースのコミットは `26cc1f1b`。
`work/k07-spectral-family.source.json` の対象 module と参照先は検査・キャッシュ保存完了、プロセスの終了0を確認した。
復旧・重複・再実行・未保存ステップは0である。
それ以前の foundations・neighborhoods・homotopy・Laurent 近似・normal forms・共通次数・座標・companion の各検査も終了0。
`algebra.Polynomial` と共通化の影響先 `polynomial_linear_algebra.Field.Representatives` の個別検査も終了0。
初回は旧 CLI のオプション不一致で終了2となり、現行 CLI の通常ビルド（終了0）で解消した。

```sh
target/debug/cli libs/topology/clutching_linearization --parse-only --save-source-snapshot work/k07-spectral-family.source.json
target/debug/cli libs/topology/clutching_linearization --source-snapshot work/k07-spectral-family.source.json --module clutching_linearization --memory-mib 8192 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 1800 --report-json work/k07-spectral-family.report.json
```

`Geometric` の有限幾何級数と `Companion.Shift` の三角行列操作も、`work/k07-geometric.source.json`・`work/k07-shift.source.json` の対象検査で保存完了・終了0。
`Shift.solveHead` と符号付きブロック順序交換も `work/k07-gauges.source.json` の対象検査で保存完了・終了0。
以後の線形同型の逆・合成 API と `Companion.With.Linearize` の安定対角化は未検証である。
これらは途中の対象検査であり、package 全依存閉包・下流・利用例・workspace の最終検証は残っている。
Laurent 行列の monic 正規化、安定線形化と clutching の比較、スペクトル束との比較、選択独立性・直和・相互逆、具体例・workspace 登録・公開一覧・下流リンク・ロードマップが残作業である。
次は Laurent 行列の正規化と companion への比較を実装する。
K07 の最終検証・PR・通常のマージと main への反映確認後、K02、B09、K03 を順番に実施する。
