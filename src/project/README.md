# Project と source の読み込み

`project` は source snapshot、外部 module、package と path dependency の読み込みを担当する。
`syntax` の parser を使って、読み込み済みの `Module` 群を構築する。

## Source snapshot

`SourceSnapshot::read` は source tree と path dependencies の内容・ファイル identity を読み込み時に固定する。
`with_file` / `without_file` は元の snapshot を保持して編集後の snapshot を作る。
メモリ上だけの source は `SourceSnapshot::new` と `insert` で構築できる。
`source` はファイルの内容、`identity` は別名を解決したファイル identity を返す。

`read_with_dependency_cache` は依存 package 自身の source tree を読み、callback が返す snapshot から推移的な依存を取り込む。
`package_snapshot` は指定 package とその path dependencies に snapshot を絞る。
キャッシュの照合・保存と semantic query は [sema](../sema/README.md) が担当する。

## Module と package の読み込み

`SourceProvider` により source の取得と parse 処理を差し替えられる。
`DiskSource` はファイルを直接読み、`sema` の provider は immutable な `SourceSnapshot` と parse cache を使う。
package loader と snapshot は同じ manifest 解釈を使う。
package loader は依存先を訪問し、package 名による import を root からの module path に結合する。

`PackageGraph` は package の依存関係と読み込み済みの AST を保持する。
