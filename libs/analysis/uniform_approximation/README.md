# Stone–Weierstrass と Laurent 近似（K04、実装中）

計画は [_plans/math/k04-uniform-approximation.md](../../../_plans/math/k04-uniform-approximation.md)。
既存の多項式・Laurent 環、実数の連続演算とコンパクト性、束の有限埋め込みを再利用する。

## 検証と再開

基点は K01 統合済み main `f6c3dcfb`、ブランチは `math/k04-uniform-approximation`。
開始時に K04 / Weierstrass の既存ブランチ・PR・実装がないことを確認した。
最後に成功した対象検査は `d46110c4` の `work/k04-real-sw`（終了0・キャッシュ保存完了）。
絶対値近似多項式・Dini 型一様化・一様閉包の代数演算・最大最小、有限被覆による格子の稠密性まで検証した。
`4c845bac` の検査の参照名エラー（終了1）は修正・再検証済み。
点の分離からの二点補間と実 Stone–Weierstrass 定理まで検証済み。
実部・虚部の抽出と複素 Stone–Weierstrass 定理の追加は未検証。
Laurent 環の公開帰納法も未検証。
[draft PR #45](https://github.com/pdf-jube-joba/ref-type/pull/45) に途中保存する。
残作業は実・複素 Stone–Weierstrass、円周・積上の係数付き Laurent 近似、有限成分評価・束自己準同型・可逆性、利用例・全体検証・完了文書・統合。
次は `cli libs --parse-only --save-source-snapshot` の後、`cli libs --source-snapshot … --module uniform_approximation --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 900 --report-json …` で対象を検査する。
検査の終了・キャッシュ保存完了が確認できるまでは成功と扱わない。
