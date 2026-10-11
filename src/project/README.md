# Project と source の読み込み

`project` は source snapshot、外部 module、package と path dependency の読み込みを担当する。
`syntax` の parser を使って、読み込み済みの `Module` 群を構築する。

## Source snapshot

`SourceSnapshot::read` は source tree と path dependencies の内容・ファイル identity を読み込み時に固定する。
`with_file` / `without_file` は元の snapshot を保持して編集後の snapshot を作る。
メモリ上だけの source は `SourceSnapshot::new` と `insert` で構築できる。
`source` はファイルの内容、`identity` は別名を解決したファイル identity を返す。

`SourceCache` は source の割り当てと SHA-256 digest を保持し、`read_with_source_cache` が取得を集約する。
取得時は毎回ディスクの内容を確認し、一致したファイルの text と digest を共有する。
保持量は既定64 MiB・16,384ファイルまでで、直近2回の取得で参照したファイルを残す。
`content_digest` は snapshot の内容に対応する digest を一度だけ計算し、編集したファイルだけ別の digest を持つ。
呼出側が保持する snapshot の寿命は source cache の回収と独立している。

`read_with_dependency_cache` はすべての到達可能な依存 package の source tree を読み、内容が一致する保存済み source の割り当てを共有する。
推移的な依存の内容も現在のディスクから確認する。
`package_snapshot` は指定 package とその path dependencies に snapshot を絞る。
キャッシュの照合・保存と semantic query は [sema](../sema/README.md) が担当する。

## Module と package の読み込み

`SourceProvider` により source の取得と parse 処理を差し替えられる。
`DiskSource` はファイルを直接読み、`sema` の provider は immutable な `SourceSnapshot` と parse cache を使う。
package loader と snapshot は同じ manifest 解釈を使う。
package loader は依存先を訪問し、package 名による import を root からの module path に結合する。

`PackageGraph` は package の依存関係と読み込み済みの AST を保持する。
`PackageInfo` は正規化した root による `PackageInstanceId`、名前付き直接依存、manifest と source identity の一覧を保持する。
同じ root を指す diamond dependency は一つの instance にまとめ、異なる root の package は別の instance として扱う。
