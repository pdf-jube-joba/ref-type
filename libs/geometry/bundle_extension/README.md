# 閉部分空間からの束の延長（B09）

作業中。実数値・複素数値の Tietze 延長は `bundle_extension.Extension.Real.tietze` と `Complex.tietze`。
まず閉部分空間内の閉集合の像が周囲の空間でも閉じることを証明し、Urysohn の分離関数による実関数の一様近似と Tietze 延長を構成する。
続いて実・複素射影行列の近傍への延長、束写像・同型、安定化と縮小による比較を構成する。

## 保存・再開

基点は K02 の PR #47 を統合した main `29f3f43b7a760485ad516dec1c6835d6e09aa41e`。
K02 は公開入口・依存閉包・例393モジュール、および workspace 全体8,149モジュールで accepted・終了0・保存失敗0を確認済み。
[PR #48](https://github.com/pdf-jube-joba/ref-type/pull/48) は main `d6ecc14d499efbd782a70ae5c837c4da97c7abc8` に統合済みである。
残作業はこの main からの専用ブランチ `math/b09-complete-extension` で継続する。
継続作業の [PR #49](https://github.com/pdf-jube-joba/ref-type/pull/49) は draft である。
`topology.Topology.Subspace.Closed.imageClosed` は依存閉包を含め accepted・終了0・保存失敗0（`closed.json`）。
`bundle_extension.Extension.Real.Separation.exists` に、閉集合上の連続実関数の二つの水準集合を分離する連続関数を構成した。依存を含む192モジュールで accepted・終了0・保存失敗0（`separation.json`）。
`Correction.error` と `Real.Approximation.exists` は、補正の大きさを半径の半分以下、誤差を4分の3以下にする近似を構成し、accepted・終了0・保存失敗0（`correction.json`・`approximation.json`）。
`Radii`・`MetricBudget`・`Real.Iteration.Sequence.Limit` で反復列の有界性・一様 Cauchy 性・連続な極限と元の関数への一致を証明した。
実数値の `Real.tietze` は空の場合も含め accepted・終了0・保存失敗0（`real-tietze.json`）。
複素数値の `Complex.tietze` は実部・虚部の延長を組み合わせ、accepted・終了0・保存失敗0（`complex-tietze.json`）。
次は `Extension.Real.tietze`・`Complex.tietze` を各行列成分へ適用し、閉集合上の射影行列の延長を構成する。
その後、開近傍上で射影性を回復する構成を証明し、束・束写像・同型の延長、安定化と縮小による比較、具体例、全体検証へ進む。
共有キャッシュは `libs/refcache`。
束の延長と具体例、全体検証は未完了。K03 は未着手。

今回の追加は `Real.Components`・`Complex.Components` の成分族の延長と、`Real.Matrices`・`Complex.Matrices` の有限矩形行列の延長であり、まだ未検証である。
`Real.Square`・`Complex.Square` に可逆行列の近傍への延長と連続な逆行列を追加した。
`Complex.Spectral` は単位円上のスペクトルを避ける行列族を開近傍へ延長し、K06 のスペクトル射影と像束へ接続する。
K06 の `Circle.At.domainOff` と `At.Neighborhood.open` も追加したが、これらを含め今回の数学変更はすべて検査待ちである。
一点空間上の実・複素恒等行列（次元0と1）の延長を `Extension.Examples` に追加した。
`Square.Near` では近傍から閉部分空間への制限について、行列と逆行列の一致も公開する。
`Sections.Through` に有限埋め込みと射影による切断の延長を追加し、`RealSections.extend`・`ComplexSections.extend` で成分ごとの Tietze 延長と組み合わせた。
切断の延長も未検証である。
既存 CLI は現在の引数形式に対応しない古い版だったため、`source /workspace/ref-type-env.sh` 後に `cargo build -p cli --locked` でビルドし、終了0を確認した。
`Complex.Spectral.Near` の型の参照パスを修正した後の package の構文検査は終了0である。
実成分延長の型検査は中断終了130であり、成功扱いにはしていない。
次は固定 snapshot と共有キャッシュで追加入口と依存閉包を検査し、行列から束への延長を続ける。
