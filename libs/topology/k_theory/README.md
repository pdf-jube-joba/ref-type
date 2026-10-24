# 束の Grothendieck 環（K01、実装中）

計画は [_plans/math/k01-grothendieck-k.md](../../../_plans/math/k01-grothendieck-k.md)。
B03 の射影表示と束の同型類、B02 の束演算、既存の `algebra.GroupCompletion` を再利用する。

## 検証と再開

基点は B04 統合済み main `4f411dda`、ブランチは `math/k01-grothendieck-k`。
開始時に既存の K01 / Grothendieck ブランチ・PR・実装がないことを確認した。
複素束の同型類と一般の束との比較、直和の類、直和の代表独立性と商集合上の二項演算への降下を追加した（未検証）。
[draft PR #44](https://github.com/pdf-jube-joba/ref-type/pull/44) に保存する。
`0a2c81ac` の最初のスコープ検査は `work/k01-classes` で実行中。
`0a2c81ac` の最初の対象スコープ577 module は保存完了・終了0で成功した（`work/k01-classes`）。
その後の直和の商への降下、一般の束に対する直和の類の式、代表の存在と自明束の類は未検証。
残作業は同型類の直和モノイド・テンソル半環、群完成と安定同型判定、引き戻し・ランク・被約群、有限離散空間の計算と利用例、文書・最終検証・統合である。
次は共有キャッシュを使い `libs --module topological_k_theory` を snapshot 付きで検査し、通常の型エラーを修正する。
