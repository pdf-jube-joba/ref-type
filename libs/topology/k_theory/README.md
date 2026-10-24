# 束の Grothendieck 環（K01）

コンパクト Hausdorff 空間上の複素束から、Grothendieck の可換環 \(K^0\) を構成する。
[B03 の同型類と補束](../../geometry/bundle_complements/README.md)、[B02 の束演算](../../geometry/bundle_operations/README.md)、既存の [`algebra.GroupCompletion`](../../algebra/basic/README.md) を再利用する。

## 公開 API

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

基点は B04 統合済み main `4f411dda`、作業は `math/k01-grothendieck-k` / [PR #44](https://github.com/pdf-jube-joba/ref-type/pull/44)。
全要件の実装を含む `d48cc565` の package・全依存閉包は `work/k01-package` で保存完了・終了0（4,236件検査／4,345件再利用、53,089ステップ、復旧・重複・再実行・失われたステップ・保存失敗は各0）。
対象スコープ・利用例は `bac1d6e9` の `work/k01-complete`（841 module、保存完了・終了0）でも成功した。
package コマンドは `target/debug/cli libs/topology/k_theory --source-snapshot work/k01-package.source.json --memory-mib 8192 --cache-budget-mib 12288 --time-limit-seconds 1800 --report-json work/k01-package.json`。
その後の変更は完了ドキュメントのみで、数学ソースの未検証変更はない。
次は `target/debug/cli libs --parse-only --save-source-snapshot work/k01-workspace.source.json` で固定し、`target/debug/cli libs --source-snapshot work/k01-workspace.source.json --memory-mib 10240 --cache-budget-mib 12288 --time-limit-seconds 7200 --report-json work/k01-workspace.json` を実行する。
workspace の終了・保存を確認した後に PR と必要な CI を確認し、通常の merge と main の反映確認を行う。
