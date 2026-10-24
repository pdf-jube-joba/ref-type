# Stone–Weierstrass と Laurent 近似（K04、実装中）

計画は [_plans/math/k04-uniform-approximation.md](../../../_plans/math/k04-uniform-approximation.md)。
既存の多項式・Laurent 環、実数の連続演算とコンパクト性、束の有限埋め込みを再利用する。

## 検証と再開

基点は K01 統合済み main `f6c3dcfb`、ブランチは `math/k04-uniform-approximation`。
開始時に K04 / Weierstrass の既存ブランチ・PR・実装がないことを確認した。
最後に成功した対象検査は `11fca362` の `work/k04-closure`（共有キャッシュ保存完了・終了0）。
絶対値近似多項式・Dini 型一様化・一様閉包の代数演算と極限まで検証した。
`4c845bac` の `work/k04-lattice-closure` は参照名 `Real.ltTrans` が見つからず終了1。
この参照を `Order.ltTrans` に修正し、最大・最小への閉性、有限被覆による下側近似を追加した状態は未検証。
Laurent 環の公開帰納法も未検証。
[draft PR #45](https://github.com/pdf-jube-joba/ref-type/pull/45) に途中保存する。
残作業は実・複素 Stone–Weierstrass、円周・積上の係数付き Laurent 近似、有限成分評価・束自己準同型・可逆性、利用例・全体検証・完了文書・統合。
次は `cli libs --parse-only --save-source-snapshot` の後、`cli libs --source-snapshot … --module uniform_approximation --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 900 --report-json …` で対象を検査する。
検査の終了・キャッシュ保存完了が確認できるまでは成功と扱わない。
