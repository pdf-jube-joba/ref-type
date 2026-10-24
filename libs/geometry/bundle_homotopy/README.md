# 束のホモトピー不変性と clutching（B04、実装中）

計画は [_plans/math/b04-bundle-homotopy.md](../../../_plans/math/b04-bundle-homotopy.md)。
B03 の計量・有限埋め込み・射影の像束、K06 の近接射影比較と区間の局所から大域への原理、B02 の束演算を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 検証と再開

基点は K06 の統合済み main `75e87a4c`、ブランチは `math/b04-bundle-homotopy`。
開始時にリモートの B04 ブランチ・open PR がないことを確認した。
作業は [draft PR #43](https://github.com/pdf-jube-joba/ref-type/pull/43) に保存する。
最後に対象検査が成功したコミットは `33fadf17`（円板の pushout と球面の同相のスコープ）。
両端の束の比較、ホモトピックな引き戻し、指定部分集合上で恒等となる比較、cofibration に沿う自己同型の延長を実装した。
共有キャッシュで `ProjectionComparison`、`Projections.Homotopy`、`Cylinder`、`For.Pullbacks.Along`、`For.Pullbacks.Relative`、`Projections.Operators.Units`、`Projections.ImageAutomorphism`、`Projections.Moved`、`Projections.Isotopy`、`For.Extensions` を検査し、それぞれプロセス・保存処理の正常終了（終了0）を確認した。
最後の `For.Extensions` は参照依存先を含む734 moduleで成功した。
修正前の参照・型エラーは終了1、引数の表記ミスは終了2であり、修正後に対象を再検証した。

`15f8e0f7` の二開集合での clutching は局所枠・遷移式を含む対象検査が終了0で成功した。
`ec020933` の球面上の clutching と実際の円板への制限束の自明化（`.Disks`）も対象検査が終了0で成功した。
`6ca0466f` の一般の二束間の相対同型の延長（`.For.Extensions.To` を含む検査）も終了0で成功した。
`370dd74b` の局所枠から指定した cocycle への比較（`.FromCharts`）も終了0で成功した。
`699c5f51` の clutching と引き戻しの比較も対象検査が終了0で成功した。
`33fadf17` の円板の pushout と球面の同相は対象検査が終了0で成功した。
clutching 関数のホモトピーによる束同型、閉被覆に沿う束射・束同型の貼り合わせ、連続なブロック対角作用素と直和による clutching の比較、円板の同型を比較する半球上の座標表示、境界で両立する gauge からの束同型とその逆向きの構成は未検証の WIP である。
`.Clutching.Homotopy` の合成部分の検査は未完了である。
2回は終了2・`memory-limit`（4,294,967,296 byte の allocation failure）、その後の修正・計測は120〜180秒上限で終了2・`time-limit` となった。
最新の `d26d43f8` の計測は `startInverseExists` の検査で180秒上限に達した。
環境・端末・ファイル操作は利用でき、原因の調査と型の具体化の整理を継続する。
B01 の逆同型の存在、B02 の同型の合成・直和の存在を公開 API として追加したため、これらと下流も最終検査に含める。

検査は `target/debug/cli libs --parse-only --save-source-snapshot work/<name>-snapshot.json`、続いて `target/debug/cli libs --module <scope> --source-snapshot work/<name>-snapshot.json --memory-mib 8192 --time-limit-seconds 900 --diagnostics compact --report-json work/<name>.json --cache-stats` を使用する。
次は `.ClosedCover` と `.BlockDiagonal` を検査し、`.Clutching.Homotopy` の型の具体化をさらに計測して修正し、終了コードを確認する。
残作業は一般の同型への相対延長、円板の clutching のホモトピー・安定化・同型の対応、実・複素の利用例、文書・依存リンク、package全体・依存先・影響箇所・workspace の最終検査である。
