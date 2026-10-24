# 束の Grothendieck 環（K01、実装中）

計画は [_plans/math/k01-grothendieck-k.md](../../../_plans/math/k01-grothendieck-k.md)。
B03 の同型類と補束、B02 の束演算、既存の `algebra.GroupCompletion` を再利用する。

## 公開 API（追加分は検査中）

`KTheory.On[X, baseSpace, compact, hausdorff]` はコンパクト Hausdorff 空間上の複素束を扱う。
`Bundle.value` と `Compare.criterion` が一般の束を B03 の射影表示の同型類と比較する。
`AdditiveMonoid`・`MultiplicativeMonoid`・`Semiring` は B02 の実際の束同型から演算の法則を導く。
`K0` は既存の半環の群完成を用いる可換環で、`Stability.ForBundles.criterion` は同じ自明束を加える安定同型による等式判定である。
`Pullback.K0.map`、`IdentityPullback.onK0`、`Pullback.Composition.onK0` が反変関手を与える。
`Pullback.Ranks.naturality` はランクと引き戻しの可換性を証明する。
`Pullback.Ranks.Reduced` は基点を保つ写像による被約群の引き戻しである。
`Ranks.rank` は局所定数な整数値ランク、`Ranks.Reduced[point].group` は基点でのランクの核である。
`VariableRanks` は離散底上に任意の自然数値ランクを持つ束を構成する。
`FiniteDiscrete.Classification` はランクによる束の分類、`FiniteDiscrete.Computation` と `Point` は整数値関数群・整数群との往復写像と逆写像則を与える。
`Examples` は空空間・一点・二点上の正負のランクを検査する。

## 検証と再開

基点は B04 統合済み main `4f411dda`、作業は `math/k01-grothendieck-k` / [draft PR #44](https://github.com/pdf-jube-joba/ref-type/pull/44)。
最後の検証成功は `31c15b37` の `work/k01-functor-rank2`（対象800 module、保存完了、終了0、保存失敗0）。
分配則・零の吸収則・Grothendieck 環・自明束による安定同型判定・引き戻し環写像・整数値ランクを追加した。
直和ランク公式、ランクの群完成への延長・被約群、引き戻しの恒等・合成則、離散底上の線形写像族から連続な束写像への構成を追加した。
有限離散束の分類・K 群計算、一点計算・利用例、ランクの自然性を追加した（未検証）。
`1fb39649` の `work/k01-computation` は有限部分集合の帰納法に渡す述語の形式で終了1、集合内包へ修正した。
各検査は `target/debug/cli libs --source-snapshot work/<名前>.source.json --module topological_k_theory --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 1200 --report-json work/<名前>.json` で共有キャッシュを利用する。
次は修正版を snapshot 化して同じ対象検査を行い、終了コード・保存完了を確認する。
有限離散底・一点の計算、空・一点・二点の利用例、引き戻しに対するランクの自然性を追加した（未検証）。
残作業は追加分の検査・修正、一点計算・自然性と利用例、文書・最終検証・統合。
