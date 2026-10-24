# 束のホモトピー不変性と clutching（B04、実装中）

計画は [_plans/math/b04-bundle-homotopy.md](../../../_plans/math/b04-bundle-homotopy.md)。
B03 の計量・有限埋め込み・射影の像束、K06 の近接射影比較と区間の局所から大域への原理、B02 の束演算を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 公開 API（最終検証中）

入口は `bundle_homotopy.Homotopy[].Over`。

| API | 構成・証明 |
| --- | --- |
| `Cylinder.endpointIsomorphismExists` | コンパクト Hausdorff 空間と区間の積上の束の両端を比較する |
| `For.Pullbacks.Along` / `Relative` | ホモトピックな引き戻しを比較し、固定部分集合での恒等性を示す |
| `For.Extensions` / `To` | cofibration に沿う自己同型・二束間同型の相対延長 |
| `For.Contractible` / `Disks.Triviality` | 収縮可能なコンパクト空間・閉円板上の任意の束を自明化する |
| `Clutching.With` / `Pullback` | 二開集合の遷移関数から束を作り、引き戻しとの比較同型を構成する |
| `Clutching.Homotopy` / `With.Sum` / `With.Stabilize` | 遷移関数のホモトピー、ブロック直和・安定化を束の同型へ送る |
| `Disks.Hemispheres.Cover` | 二円板の pushout と球面の実際の同相・閉半球での貼り合わせ |
| `Disks.Clutched` / `Homotopy` | 境界球面の GL 値関数による clutching と円板制限の自明化 |
| `Disks.Clutched.Comparison.diskGaugeCriterion` | 両円板上の連続 gauge の境界での両立条件と束同型の存在の同値 |
| `Homotopy.Examples.Mobius` / `CircleLine` | 実の符号遷移・複素単位円遷移による具体的な線束 |

比較の条件は \(h_-g=g' h_+\) である。
実の場合も同じ API を用いるため、同型の判定には両円板上の gauge を明示している。

## 検証と再開

基点は K06 の統合済み main `75e87a4c`、ブランチは `math/b04-bundle-homotopy`。
開始時にリモートの B04 ブランチ・open PR がないことを確認した。
作業は [draft PR #43](https://github.com/pdf-jube-joba/ref-type/pull/43) に保存する。
最後に対象検査が成功したコミットは `4f08461d`（連続なブロック対角作用素のスコープ）。
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
clutching 関数のホモトピーによる束同型、直和による clutching の比較、円板上の任意の束の自明化、円板の同型を比較する半球上の座標表示、境界で両立する gauge からの束同型とその逆向きの構成は未検証の WIP である。
`.Clutching.Homotopy` の合成部分の検査は未完了である。
2回は終了2・`memory-limit`（4,294,967,296 byte の allocation failure）、その後の修正・計測は120〜180秒上限で終了2・`time-limit` となった。
最新の `d26d43f8` の計測は `startInverseExists` の検査で180秒上限に達した。
全 cost/bridge 計測（90秒上限、終了2）では、`bridge lower` 内の停滞を確認した。
型の変換処理に cost 計測を追加したビルドは終了0。
その計測も120秒上限で終了2・未完了となった。
`afc847e1` の allocation stack 計測（`work/b04-allocation`、360秒上限）は約295秒で終了2・memory-limit。
具体化された定義を kernel に登録する際の型変換で、`calculus::substitute` の `Cache::insert` にある scratch write 記録が4 GiBを確保しようとして失敗した。
連続な非零スカラーから GL への構成と、実 Möbius 型・複素円周 clutching の利用例を追加したが、これらは未検証である。
kernel の scratch write journal を重複排除し、キャッシュから除去した項目の記録も回収する修正を追加した。
`cargo test -p kernel --lib` は76テスト成功・終了0（長時間 scratch の記録上限と最終値の整理の回帰テストを含む）。
この修正後の B04 対象検査は未実施。
`work/b04-cache-fixed` の初回検査は通常ビルド終了前に開始したため中断し、終了130・未完了として扱う。
球面の clutching ホモトピーを一般の二開集合の構成へ送る `.Disks.Homotopy` を追加した（未検証）。
型変換時の連続した lambda 適用も一括置換へ変更した。
`cargo test -p kernel --lib` は引数の順序・自由変数・不一致の回帰検査を含む77テスト成功・終了0。
この一括置換を含む処理系での B04 検査は未実施。
通常ビルドは終了0。
scratch journal 修正だけを含む `work/b04-cache-fixed2` は、742/744 module 後も同じ定義で停滞したため、新しい一括置換のビルド完了後に中断した（終了130・未完了）。
一括置換も含む `3f74dd33` の検査 `work/b04-beta` は、605秒時点で同じ定義に停滞し、捕捉引数の比較改善へ切り替えるため中断した（終了130・未完了、保存処理を含む全体約626秒）。
円板上の gauge の存在と束同型の存在の同値 `diskGaugeCriterion` を追加した（未検証）。
`rustfmt` は選択された Rust 1.95 toolchain に未導入のため実行できず、追加箇所の整形は手動で行った。
透明な同一定義の比較で、展開した式に使われる捕捉引数だけを比較する修正を追加した。
使われない引数の型検査は維持し、不正な型の引数を拒否する回帰検査を含め、`cargo test -p kernel --lib` は78テスト成功・終了0。
比較最適化の通常ビルドは終了0。
追加の引数個数チェックを含む `e361f34a` の全 kernel テスト・通常ビルドを再実行し、続いて `.Clutching.Homotopy` を900秒上限で検査する（`work/b04-captures-final-*`）。
共有キャッシュの保持上限は `--cache-budget-mib 16384` とする。
環境・端末・ファイル操作は利用できる。
B01 の逆同型の存在、B02 の同型の合成・直和の存在を公開 API として追加したため、これらと下流も最終検査に含める。

検査は `target/debug/cli libs --parse-only --save-source-snapshot work/<name>-snapshot.json`、続いて `target/debug/cli libs --module <scope> --source-snapshot work/<name>-snapshot.json --memory-mib 8192 --time-limit-seconds 900 --diagnostics compact --report-json work/<name>.json --cache-stats` を使用する。
次は `.Clutching.Homotopy` の型の具体化を全 cost/bridge 計測で調べ、`.Clutching.With.Stabilize` と `.Disks.Clutched.Comparison` を検査し、終了コードを確認する。
残作業は一般の同型への相対延長、円板の clutching のホモトピー・安定化・同型の対応、実・複素の利用例、文書・依存リンク、package全体・依存先・影響箇所・workspace の最終検査である。
