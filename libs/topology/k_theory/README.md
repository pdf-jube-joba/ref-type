# 束の Grothendieck 環（K01、実装中）

計画は [_plans/math/k01-grothendieck-k.md](../../../_plans/math/k01-grothendieck-k.md)。
B03 の射影表示と束の同型類、B02 の束演算、既存の `algebra.GroupCompletion` を再利用する。

## 検証と再開

基点は B04 統合済み main `4f411dda`、ブランチは `math/k01-grothendieck-k`。
開始時に既存の K01 / Grothendieck ブランチ・PR・実装がないことを確認した。
複素束の同型類、直和の商への降下、一般の束との比較、直和可換モノイドを実装した。
最後の検証成功は `157545a4`、`work/k01-monoid2`（対象595 module、保存完了・終了0）。
テンソル積の類・商への降下・乗法可換モノイド、分配則・零の吸収則、群完成の環、B03 の補束を使う自明束による安定判定を追加した（未検証）。
`aed15a7f` のテンソルモノイド検査 `work/k01-tensor` は実行中。
残作業は分配則・零の吸収則、群完成・安定同型判定、引き戻し・ランク・被約群、有限離散計算・利用例、文書・最終検証・統合。
次は共有キャッシュで `libs --module topological_k_theory` を snapshot 付きで検査する。
