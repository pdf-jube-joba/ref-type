# Project と source の読み込み

`project` は source snapshot、外部 module、package と path dependency の読み込みを担当する。
`syntax` の parser を使って、読み込み済みの `Module` 群を構築する。

`SourceProvider` により source の取得と parse 処理を差し替えられる。
`DiskSource` はファイルを直接読み、`sema` の provider は immutable な `SourceSnapshot` と parse cache を使う。
`SourceSnapshot::read` がファイル内容と identity を取り込み、buffer 編集は新しい snapshot を作る。
package loader と snapshot は同じ manifest 解釈を使う。
package loader は依存先を訪問し、package 名による import を root からの module path に結合する。

`PackageGraph` は package の依存関係と読み込み済みの AST を保持する。
`sema` は `SourceSnapshot` を再公開し、従来の問い合わせ API からも利用できる。
