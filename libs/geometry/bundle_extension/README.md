# 閉部分空間からの束の延長（B09）

作業中。実数値の Tietze 延長は `bundle_extension.Extension.Real.tietze`。
まず閉部分空間内の閉集合の像が周囲の空間でも閉じることを証明し、Urysohn の分離関数による実関数の一様近似と Tietze 延長を構成する。
続いて実・複素射影行列の近傍への延長、束写像・同型、安定化と縮小による比較を構成する。

## 保存・再開

基点は K02 の PR #47 を統合した main `29f3f43b7a760485ad516dec1c6835d6e09aa41e`。
K02 は公開入口・依存閉包・例393モジュール、および workspace 全体8,149モジュールで accepted・終了0・保存失敗0を確認済み。
B09 の作業ブランチは `math/b09-bundle-extension`。
`topology.Topology.Subspace.Closed.imageClosed` は依存閉包を含め accepted・終了0・保存失敗0（`closed.json`）。
`bundle_extension.Extension.Real.Separation.exists` に、閉集合上の連続実関数の二つの水準集合を分離する連続関数を構成した。依存を含む192モジュールで accepted・終了0・保存失敗0（`separation.json`）。
`Correction.error` と `Real.Approximation.exists` は、補正の大きさを半径の半分以下、誤差を4分の3以下にする近似を構成し、accepted・終了0・保存失敗0（`correction.json`・`approximation.json`）。
`Radii`・`MetricBudget`・`Real.Iteration.Sequence.Limit` で反復列の有界性・一様 Cauchy 性・連続な極限と元の関数への一致を証明した。
実数値の `Real.tietze` は空の場合も含め accepted・終了0・保存失敗0（`real-tietze.json`）。
次は複素数値の延長を座標ごとに構成し、射影行列から束の近傍への延長へ進む。
共有キャッシュは `libs/refcache`。
複素数値・束の延長と具体例、全体検証は未完了。K03 は未着手。
