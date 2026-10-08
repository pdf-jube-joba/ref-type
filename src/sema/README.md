# Semantic API とキャッシュ

`sema::Database` は immutable な `SourceSnapshot` から検査結果を計算する。
CLI と LSP が同じ API を利用する。
crate ごとの役割は [言語処理系](../../doc/book/src/language/implementation.md) を参照。

## API

```rust
use sema::{Database, ParseKind, SourceSnapshot};

let source = SourceSnapshot::read("libs/std")?;
let mut db = Database::with_cache("libs/std/refcache");
let checked = db.check(&source);
assert!(checked.is_success());

let path = "libs/std/src/Data/Nat.ref";
let edited = source.with_file(path, std::fs::read_to_string(path)?);
let parsed = db.parse(&edited, path, ParseKind::Module);
```

snapshot は source tree と path dependencies の内容・ファイル identity を読み込み時に固定する。
`with_file` / `without_file` は元の snapshot を保持して編集後の snapshot を作る。
メモリ上だけの source は `SourceSnapshot::new` と `insert` で構築できる。

| 問い合わせ | 結果 |
| --- | --- |
| `Database::parse` / `parse_project` | ファイルの構文と診断 / package 全体の module 構文 |
| `Database::module` / `file` / `check` | module / ファイル / project 全体の semantic result |
| `Database::declaration` | 指定した宣言の情報を含む semantic result |
| `SemanticResult::declaration` | `DeclarationId` に対応する宣言 |
| `definition_at` / `references_to` / `type_at` | 参照先・参照箇所・表示用の型 |
| `all_diagnostics` / `goals` / `outputs` | 診断・ゴール・query 出力 |

位置は絶対パスと UTF-8 byte offset の半開区間で表す。
宣言 ID は module path と宣言名からなり、constructor と型関連 item は `Type::member` を使う。
`Verified` は kernel の検証完了、`Incomplete` は失敗時の途中結果を表す。
詳細診断では失敗後も独立した scope を検査する。

## 再利用

parse cache はファイル identity・内容・解析方式、semantic cache は module とその依存関係をキーにする。
未変更の問い合わせは同じ `Arc<SemanticResult>` を返し、失敗結果も実行中に再利用する。
変更時には該当 module と利用者を無効化し、検査順の一致する prefix checkpoint から再開する。
早い位置の変更や module 構成の変更では、未変更の module も再検査する場合がある。
`clear_memory` は query・parse・環境 checkpoint の保持結果を解放する。

永続キャッシュは検証済みの semantic result を JSON、raw / kernel の共有 arena と環境を圧縮した checkpoint を `.env` に保存する。
キーには source・依存関係・manifest・検査設定・checker の実装と toolchain の fingerprint を含める。
破損・形式違い・読み込み失敗は再計算し、保存失敗は検証結果を変えず統計に記録する。
サイズ上限や保存候補の選択は [environment.rs](src/environment.rs)、実装 fingerprint は [build.rs](build.rs) を参照。

package 全体の検証に成功すると、package ごとに依存先のソースとファイル identity を含む snapshot を `.sources.json` に保存する。
`Database::read_snapshot(path, true)` は依存 package 自身のソース・manifest・checker の fingerprint を照合し、一致する snapshot の推移的な依存を取り込む。
`CheckOptions::force_local` は入口 package を再検査し、依存 package の結果と入口より前の環境 checkpoint を再利用する。
`CheckOptions::progress` は子 module を含むソース module ごとの検査・省略と所要時間を通知する。

## CLI と検証

リポジトリのルートで同じコマンドを二度実行すると、別プロセスでの再利用を確認できる。

```sh
cargo run -p cli --release --locked -- libs/std --cache-stats
cargo run -p cli --release --locked -- libs/std --cache-stats
cargo run -p cli --release --locked -- libs/std --no-cache
cargo run -p cli --release --locked -- libs/std --full-check
cargo run -p cli --release --locked -- libs/std --full-check-local
```

`--no-cache` は永続キャッシュの読み書きを無効にし、`--full-check` は依存先を含む全体の再検証後にキャッシュを更新する。
`--full-check-local` は指定した package を再検証し、依存先は自身の変更を照合してキャッシュを再利用する。
保存先などの指定は [利用方法](../USAGE.md#検査とキャッシュ) を参照。
`environment_hits` は復元した checkpoint 数、`restored_modules` は復元で検査を省略した module 数、`environment_bytes` は保持中の圧縮 checkpoint の合計サイズである。

[semantic API のテスト](tests/semantic.rs) は編集、依存変更、位置情報、永続化と破損時の再構築を確認する。
[incremental example](examples/incremental.rs) は buffer 編集後の結果と全再構築の一致も検査する。

```sh
cargo test -p sema --locked
cargo run -p sema --release --locked --example incremental -- libs/std libs/std/src/Alg/Alg.ref
```
