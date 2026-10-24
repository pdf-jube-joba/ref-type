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
最後の検証成功は `2f8ba902`、`work/k01-ring-computation`（対象838 module、保存完了、終了0、保存失敗0）。
環構成・安定判定・反変関手・整数ランクと自然性・被約群・有限離散束の分類と加法群計算・一点の乗法整合性は対象検査済み。
その後の整数値関数環、有限離散・一点の環同型、環同型を使う利用例、一般の差の安定等式判定が未検証。
`bac1d6e9` を `work/k01-complete.source.json` に固定した対象検査が進行中。
コマンドは `target/debug/cli libs --source-snapshot work/k01-complete.source.json --module topological_k_theory --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 1200 --report-json work/k01-complete.json`。
次は終了コードと保存結果を確認し、通常の型エラーを修正する。
その後は package 全依存閉包・workspace を共有キャッシュで検査し、下流リンク・ロードマップ・PR を整えて統合する。
