# 束のホモトピー不変性と clutching（B04、実装中）

計画は [_plans/math/b04-bundle-homotopy.md](../../../_plans/math/b04-bundle-homotopy.md)。
B03 の計量・有限埋め込み・射影の像束、K06 の近接射影比較と区間の局所から大域への原理、B02 の束演算を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 検証と再開

基点は K06 の統合済み main `75e87a4c`、ブランチは `math/b04-bundle-homotopy`。
開始時にリモートの B04 ブランチ・open PR がないことを確認した。
作業は [draft PR #43](https://github.com/pdf-jube-joba/ref-type/pull/43) に保存する。
検証済みの最新コミットは `821023d4`（相対延長までの対象スコープ）。
両端の束の比較、ホモトピックな引き戻し、指定部分集合上で恒等となる比較、cofibration に沿う自己同型の延長を実装した。
共有キャッシュで `ProjectionComparison`、`Projections.Homotopy`、`Cylinder`、`For.Pullbacks.Along`、`For.Pullbacks.Relative`、`Projections.Operators.Units`、`Projections.ImageAutomorphism`、`Projections.Moved`、`Projections.Isotopy`、`For.Extensions` を検査し、それぞれプロセス・保存処理の正常終了（終了0）を確認した。
最後の `For.Extensions` は参照依存先を含む734 moduleで成功した。
修正前の参照・型エラーは終了1、引数の表記ミスは終了2であり、修正後に対象を再検証した。

`15f8e0f7` の二開集合での clutching は局所枠・遷移式を含む対象検査が終了0で成功した。
`ec020933` の球面上の clutching と実際の円板への制限束の自明化（`.Disks`）も対象検査が終了0で成功した。
一般の二束間の相対同型の延長、局所枠から既存の cocycle への比較、pushout の帰納法の公開は未検証の WIP である。
検査は `target/debug/cli libs --parse-only --save-source-snapshot work/<name>-snapshot.json`、続いて `target/debug/cli libs --module <scope> --source-snapshot work/<name>-snapshot.json --memory-mib 8192 --time-limit-seconds 900 --diagnostics compact --report-json work/<name>.json --cache-stats` を使用する。
次は `.For.Extensions`、`.FromCharts` を対象検査し、終了コードを確認する。
残作業は一般の同型への相対延長、円板の clutching のホモトピー・安定化・同型の対応、実・複素の利用例、文書・依存リンク、package全体・依存先・影響箇所・workspace の最終検査である。
