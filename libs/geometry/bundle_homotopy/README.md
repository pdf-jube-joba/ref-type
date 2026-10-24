# 束のホモトピー不変性と clutching（B04、実装中）

計画は [_plans/math/b04-bundle-homotopy.md](../../../_plans/math/b04-bundle-homotopy.md)。
B03 の計量・有限埋め込み・射影の像束、K06 の近接射影比較と区間の局所から大域への原理、B02 の束演算を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 検証と再開

基点は K06 の統合済み main `75e87a4c`、ブランチは `math/b04-bundle-homotopy`。
開始時にリモートの B04 ブランチ・open PR がないことを確認した。
近接射影間の比較を実・複素共通のスカラーに移す最初の構成を追加した。
未検証の WIP であり、最後の検証済み入力は K06 main の workspace 7,441 module（終了コード0）である。
次は workspace の構文解析と `bundle_homotopy.Homotopy.Over.ProjectionComparison` の対象検査を共有キャッシュで実行する。
残作業は両端の比較、ホモトピックな引き戻し、相対的な同型の延長、円板の clutching とホモトピー・安定化・同型の対応、利用例、全依存と下流の最終検査である。
