# clutching の安定線形化（K07、実装中）

入口は `clutching_linearization.Linearization`。
`Blocks` は二つの複素ベクトル空間の直和上で上下の剪断写像を構成し、係数の加法則・係数0での恒等性・連続族の各点で使う逆写像の両逆を証明する。

## 検証と引き継ぎ

ブランチは `math/k07-clutching-linearization`、開始点は main `744d501e`。
GitHub 連携で #42〜#45 の統合を確認済み、open PR の検索結果は空であった。
`Blocks` の剪断写像・Schur 分解・可逆な経路と、実成分の共通誤差幅を扱う `Uniform` を実装した。
K07 の Laurent 近似ホモトピー・安定線形化・スペクトル束への比較・自然性・相互逆・利用例と登録は残作業である。
`work/k07-foundations.source.json` の対象 module と参照先は `work/k07-foundations.report.json` で検査・保存完了、終了0。
コマンドは `target/debug/cli libs/topology/clutching_linearization --source-snapshot work/k07-foundations.source.json --module clutching_linearization --memory-mib 8192 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --time-limit-seconds 1800 --report-json work/k07-foundations.report.json`。
最初は旧 CLI のオプション不一致で終了2、現行 CLI の通常ビルドは終了0。
構文修正と半径補題の存在命題への修正後、現在の数学ソースは上記 snapshot と一致する。
この検査は package 全依存閉包・下流・最終検証とは別である。
最後に対象検査が成功したコミットは `76aa6917`。
`ComplexBounds`・`MatrixNeighborhoods.Perturbation` の追加と依存登録も `work/k07-neighborhoods.source.json` の対象検査で保存完了・終了0。
後者のコマンドは上記の snapshot・report 名を `k07-neighborhoods` に置き換えて実行した。
`ComplexBounds` の補題と `Perturbation.Nearby` の行列ホモトピーも `work/k07-homotopy.source.json` の対象検査で保存完了・終了0。
同じコマンドで snapshot・report 名を `k07-homotopy` とした。
`On.Matrices.exists` は連続可逆行列族の Laurent 近似、可逆なホモトピー、両端の等式を構成する。
`On.Matrices.Result` は逆行列の連続性と両逆を公開する。
この追加と K04 の評価連続性の公開は `work/k07-laurent.source.json` の対象検査で保存完了・終了0（コマンドの snapshot・report 名を `k07-laurent` とした）。
`LaurentNormal.exists` はすべての Laurent 多項式について、変数の非負整数冪を掛けた結果を既存の多項式環へ移す表示を構成する。
和・負・積の表示と評価準同型を含め `work/k07-normal.source.json` の対象検査で保存完了・終了0。
Laurent 環の係数準同型の公開もこの検査に含み、`algebra.Polynomial.Over.Finite` に可換環上の有限係数表示を追加し、`target/debug/cli libs/algebra/basic --module algebra.Polynomial --memory-mib 8192 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact --report-json work/k07-finite.report.json` は保存完了・終了0。
`LaurentNormal.FiniteForm` と `finiteExists` への接続も `work/k07-finite-normal.source.json` の対象検査で保存完了・終了0。
既存の体上の `galois` の係数演算と `polynomial_linear_algebra.Field.Representatives.exists` はこの可換環版を再利用する形へ共通化した。
影響する `polynomial_linear_algebra.Field.Representatives` の検査は `work/k07-field-representatives.report.json` で保存完了・終了0。
行列の全成分に共通の shift を選ぶ `LaurentNormal.Matrices.commonExists` も `work/k07-common.source.json` で対象検査・保存完了、終了0。
零係数による padding と `LaurentNormal.Matrices.finiteMatrixExists` は共通の shift・次数・有限係数配列を構成する。
`work/k07-degree.source.json` の対象検査は保存完了・終了0で、体上 API の共通化後の入力を含む。
有限個の座標ブロックと単一の有限座標空間の比較 `Coordinates.At.frame` も、両逆・加法・スカラーを含めて `work/k07-coordinates.source.json` で対象検査・保存完了、終了0。
`Companion.With` の作用素・多項式と `Eigen.polynomialKernel` の固有ベクトルからの比較も `work/k07-companion.source.json` で対象検査・保存完了、終了0。
`noUnitEigen` は単位円上での多項式の零核から companion の単位円固有値の不在を導く。
以後の座標成分の選択・族の連続性と `Companion.With.Spectral` の K06 接続は未検証である。
`work/k07-spectral` は兄弟 module の import パスの修正前に終了1。
その修正、companion 行列族の連続性、スペクトル像束と K0 の差の構成を含む `work/k07-spectral-family.source.json` の対象検査を実行中であり、終了結果は未確認。
次は companion 作用素とブロック操作による安定線形化へ進む。
