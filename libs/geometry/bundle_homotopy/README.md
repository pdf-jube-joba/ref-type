# 束のホモトピー不変性と clutching（B04、実装中）

計画は [_plans/math/b04-bundle-homotopy.md](../../../_plans/math/b04-bundle-homotopy.md)。
B03 の計量・有限埋め込み・射影の像束、K06 の近接射影比較と区間の局所から大域への原理、B02 の束演算を再利用する。
実・複素の両方のスカラーを扱う `Homotopy.Over` に構成を置く。

## 検証と再開

基点は K06 の統合済み main `75e87a4c`、ブランチは `math/b04-bundle-homotopy`。
開始時にリモートの B04 ブランチ・open PR がないことを確認した。
作業は [draft PR #43](https://github.com/pdf-jube-joba/ref-type/pull/43) に保存する。
近接射影間の比較を実・複素共通のスカラーに移す最初の構成を追加した。
`d7312c53` の `ProjectionComparison` は参照依存先を含む458 module・48ステップが終了コード0で成功し、保存処理の終了も確認した。
`18f1f947` の指定した部分集合上で恒等となる射影族の比較は、参照依存先を含む596 module・138ステップが終了コード0で成功した。
最初の検査は K06 への参照パスの誤りで終了コード1となり、外部 package のパスに修正して再検証した。
その後に追加した `Presentation`・`EmbeddedCylinder`・`Cylinder` は未検証の WIP である。
次は workspace の構文解析と `bundle_homotopy.Homotopy.Over.Cylinder` の対象検査を共有キャッシュで実行し、終了コードを確認する。
残作業は両端の比較、ホモトピックな引き戻し、相対的な同型の延長、円板の clutching とホモトピー・安定化・同型の対応、利用例、全依存と下流の最終検査である。
