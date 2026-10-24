# 束の Grothendieck 環（K01、実装中）

計画は [_plans/math/k01-grothendieck-k.md](../../../_plans/math/k01-grothendieck-k.md)。
B03 の同型類と補束、B02 の束演算、既存の `algebra.GroupCompletion` を再利用する。

## 公開 API（追加分は検査中）

`KTheory.On[X, baseSpace, compact, hausdorff]` はコンパクト Hausdorff 空間上の複素束を扱う。
`Bundle.value` と `Compare.criterion` が一般の束を B03 の射影表示の同型類と比較する。
`AdditiveMonoid`・`MultiplicativeMonoid`・`Semiring` は B02 の実際の束同型から演算の法則を導く。
`K0` は既存の半環の群完成を用いる可換環で、`Stability.ForBundles.criterion` は同じ自明束を加える安定同型による等式判定である。
`Stability.differenceCriterion` は一般の仮想束の差の等式を、交差直和に同じ自明束を加える判定へ帰着する。
`Pullback.K0.map`、`IdentityPullback.onK0`、`Pullback.Composition.onK0` が反変関手を与える。
`Pullback.Ranks.naturality` はランクと引き戻しの可換性を証明する。
`Pullback.Ranks.Reduced` は基点を保つ写像による被約群の引き戻しである。
`Ranks.rank` は局所定数な整数値ランク、`Ranks.Reduced[point].group` は基点でのランクの核である。
`VariableRanks` は離散底上に任意の自然数値ランクを持つ束を構成する。
`FiniteDiscrete.Classification` はランクによる束の分類、`FiniteDiscrete.Computation` は整数値関数群との往復写像を与える。
`FiniteDiscrete.RingComputation.isomorphism` と `Point.Ring.isomorphism` は、それぞれ整数値関数環・整数環との環同型である。
`Examples` は空空間・一点・二点上の正負のランクを検査する。

例えば一点上の整数に対応する仮想束は、次のように使える。

```ref
\import topological_k_theory.KTheory[].Point[] \as Point;
\import std.Arithmetic[].Int[] \as I;
\definition minusOne: Point.Carrier := Point.backward (I.Neg.specification I.One.specification);
\definition rank: Point.forward minusOne = I.Neg.specification I.One.specification := Point.rightInverse (I.Neg.specification I.One.specification);
```

同じ公開 API を使う検査対象は `KTheory.Examples` に置く。

## 検証と再開

基点は B04 統合済み main `4f411dda`、作業は `math/k01-grothendieck-k` / [draft PR #44](https://github.com/pdf-jube-joba/ref-type/pull/44)。
最後の検証成功は `bac1d6e9`、`work/k01-complete`（対象スコープ、保存完了、終了0、保存失敗0）。
環構成・反変関手・ランクと自然性・被約群・安定判定・有限離散／一点の環同型・利用例は対象検査済み。
その後の `Stability.differenceCriterion`（一般の差の判定）が未検証。
次は `target/debug/cli libs/topology/k_theory --parse-only --save-source-snapshot work/k01-package.source.json` で入力を固定する。
続いて `target/debug/cli libs/topology/k_theory --source-snapshot work/k01-package.source.json --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 1800 --report-json work/k01-package.json` で package と全依存閉包を検査し、終了コード・保存完了を確認する。
その後は workspace の検査、下流リンク・ロードマップ・PR の整備と統合を行う。
