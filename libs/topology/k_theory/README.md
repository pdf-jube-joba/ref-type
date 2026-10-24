# 束の Grothendieck 環（K01、実装中）

計画は [_plans/math/k01-grothendieck-k.md](../../../_plans/math/k01-grothendieck-k.md)。
B03 の同型類と補束、B02 の束演算、既存の `algebra.GroupCompletion` を再利用する。

## 検証と再開

基点は B04 統合済み main `4f411dda`、作業は `math/k01-grothendieck-k` / [draft PR #44](https://github.com/pdf-jube-joba/ref-type/pull/44)。
最後の検証成功は `1df12dca` の `work/k01-ring5`（対象759 module、保存完了、終了0、保存失敗0）。
分配則・零の吸収則・Grothendieck 環・自明束による安定同型判定・引き戻し環写像・整数値ランクを追加した。
直和ランク公式、ランクの群完成への延長・被約群、引き戻しの恒等・合成則を追加した（未検証）。
各検査は `target/debug/cli libs --source-snapshot work/<名前>.source.json --module topological_k_theory --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 1200 --report-json work/<名前>.json` で共有キャッシュを利用する。
次は修正版を snapshot 化して同じ対象検査を行い、終了コード・保存完了を確認する。
残作業は追加分の検査・修正、有限離散計算・利用例、文書・最終検証・統合。
