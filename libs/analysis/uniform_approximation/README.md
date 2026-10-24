# Stone–Weierstrass と Laurent 近似（K04、実装中）

計画は [_plans/math/k04-uniform-approximation.md](../../../_plans/math/k04-uniform-approximation.md)。
既存の多項式・Laurent 環、実数の連続演算とコンパクト性、束の有限埋め込みを再利用する。

## 検証と再開

基点は K01 統合済み main `f6c3dcfb`、ブランチは `math/k04-uniform-approximation`。
開始時に K04 / Weierstrass の既存ブランチ・PR・実装がないことを確認した。
最後に成功した対象検査は `2a916922` の `work/k04-bundle-density`（終了0・キャッシュ保存完了）。
実・複素 Stone–Weierstrass、円周と積の Laurent 近似、有限成分の同時近似、行列作用と圧縮の誤差評価、行列式の可逆性余裕、B03 分裂を使う束自己準同型の構成と誤差評価、射影と可換な可逆行列による束同型まで検証した。
先行検査の参照名・暗黙型・関数外延性・部分型の中間式に関する失敗（終了1）は明示式で修正・再検証済み。
射影成分の大域的上界と、単位球上での束自己準同型の一様近似は追加済み・未検証。
[draft PR #45](https://github.com/pdf-jube-joba/ref-type/pull/45) に途中保存する。
残作業は一様評価の検証、射影を保存する行列の構成・可逆性への接続、利用例・全体検証・完了文書・統合。
次は `cli libs --parse-only --save-source-snapshot` の後、`cli libs --source-snapshot … --module uniform_approximation --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 900 --report-json …` で対象を検査する。
検査の終了・キャッシュ保存完了が確認できるまでは成功と扱わない。
