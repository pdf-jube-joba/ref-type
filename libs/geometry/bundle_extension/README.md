# 閉部分空間からの束の延長（B09）

作業中。
まず閉部分空間内の閉集合の像が周囲の空間でも閉じることを証明し、Urysohn の分離関数による実関数の一様近似と Tietze 延長を構成する。
続いて実・複素射影行列の近傍への延長、束写像・同型、安定化と縮小による比較を構成する。

## 保存・再開

基点は K02 の PR #47 を統合した main `29f3f43b7a760485ad516dec1c6835d6e09aa41e`。
K02 は公開入口・依存閉包・例393モジュール、および workspace 全体8,149モジュールで accepted・終了0・保存失敗0を確認済み。
B09 の作業ブランチは `math/b09-bundle-extension`。
`topology.Topology.Subspace.Closed.imageClosed` は依存閉包を含め accepted・終了0・保存失敗0（`closed.json`）。
`bundle_extension.Extension.Real.Separation.exists` に、閉集合上の連続実関数の二つの水準集合を分離する連続関数を構成した。こちらは未検証。
次は共有キャッシュ `libs/refcache` で分離補題を検査し、閉集合上の連続実関数に対する縮小誤差付きの近似補題を構成する。
関数・束の延長の本体と具体例は未実装。K03 は未着手。
