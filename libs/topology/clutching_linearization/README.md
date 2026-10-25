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
K07 は [draft PR #46](https://github.com/pdf-jube-joba/ref-type/pull/46) で進行中。

最後に対象検査が成功した数学ソースのコミットは `67f32242`。
Laurent 近似、共通次数、座標、companion、安定対角化、monic 正規化、スペクトル像束と K0 の差の構成、積空間上の clutching 束まで検査が成功した。
`work/k07-clutched.report.json` は accepted、プロセスの終了0とキャッシュ保存完了を確認済みである。
このコミットは push 後のリモート SHA も確認済みである。

```sh
target/debug/cli libs/topology/clutching_linearization --parse-only --save-source-snapshot work/k07-clutched.source.json
target/debug/cli libs/topology/clutching_linearization --source-snapshot work/k07-clutched.source.json --module clutching_linearization --memory-mib 8192 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 1800 --report-json work/k07-clutched.report.json
```

未検証の変更は、B04 の閉被覆 gauge 比較・等しい遷移関数の比較、積空間上の gauge・ホモトピーによる比較、ブロック gauge の連続性と行列表示。
`work/k07-motion` は `Comparison` の補題で数分進まなかったため SIGINT で中断し、終了130・検証未完了として扱う。
反射的な場合を独立 module に分けた `work/k07-comparison` は300秒制限で終了2・time-limitとなり、検証未完了。
`work/k07-comparison`（300秒）と `work/k07-comparison-alias`（180秒）、trace による個別検査（90秒）は終了2・time-limit・未完了。
遷移関数から作る `Raw` cocycle を分離し、既存の `FromCharts.With` を使う構成へ変更した。
`b3f782ef` の B04 `Clutching.With.Comparison` 自身と参照先は `work/k07-cocycle-equality` で accepted・保存失敗0・終了0。
次は K07 全対象 module を検査し、閉被覆 gauge・積空間ホモトピー・ブロック線形化の連続性・スペクトル核の追加分を修正・確認する。
既存の有限係数共通化の影響先 `polynomial_linear_algebra.Field.Representatives` の個別検査は終了0。
package 全依存閉包・影響する下流・利用例・workspace の最終検証は残っている。
clutching とスペクトル束の比較、選択独立性・直和・相互逆、具体例・workspace 登録・公開一覧・下流リンク・ロードマップが残作業である。
K07 の最終検証・通常のマージと main への反映確認後、K02、B09、K03 を順番に実施する。
