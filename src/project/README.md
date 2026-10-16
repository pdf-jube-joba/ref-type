# Project と source の読み込み

`project` は source snapshot、外部 module、package・workspace と path dependency を読み込み、`syntax` の AST を構築する。

## Source snapshot

`SourceSnapshot::read` は到達可能なソースと manifest の内容・identity を固定する。
`with_file` / `without_file` は編集版を作り、`new` / `insert` はメモリ上のソースを構築する。
`source` は本文、`identity` は別名を解決したファイル identity を返す。
`package_snapshot` は指定 package とその依存先に範囲を絞る。

`SourceCache` は毎回内容を確認し、一致する text と SHA-256 digest を共有する。
既定64 MiB・16,384ファイル、直近2回の取得世代を保持する。
`read_with_source_cache` と `read_with_dependency_cache` が取得を集約し、`content_digest` は snapshot ごとの内容 digest を返す。
キャッシュの回収後も、呼出側が保持する snapshot は有効である。

## Module と package の読み込み

`SourceProvider` で取得と parse を差し替える。
`DiskSource` はディスク、[sema](../sema/README.md) は snapshot と parse cache を使う。
loader は共通依存を一度だけ訪問し、package 名の import を root からの module path に結合する。

`PackageGraph` は依存グラフと AST、`entry_packages` は検査入口を持つ。
`PackageInfo` は正規化した root による `PackageInstanceId`、名前付き直接依存、manifest、source identity を持つ。
同じ root は同じ instance、別 root は別 instance である。

workspace を入力にすると全 member と依存先を、member を入力にするとその依存閉包を読む。
両方とも workspace manifest と共通の保存先を保持する。
`workspace::default_cache_directory` は祖先の manifest から所属を調べ、`SourceSnapshot::default_cache_directory` は保持済みの所属から保存先を返す。
manifest の例と操作は [利用方法](../USAGE.md) を参照。
