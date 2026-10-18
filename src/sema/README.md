# Semantic API とキャッシュ

CLI と LSP は `sema::Database` で immutable な [SourceSnapshot](../project/README.md#source-snapshot) を検査する。
CLI の操作は [利用方法](../USAGE.md) を参照。

## API

```rust
use sema::{Database, ParseKind, SourceSnapshot};
let source = SourceSnapshot::read("libs/std")?;
let mut db = Database::with_cache(source.default_cache_directory());
let checked = db.check(&source);
assert!(checked.is_success());
let path = "libs/std/src/Data/Nat.ref";
let edited = source.with_file(path, std::fs::read_to_string(path)?);
let parsed = db.parse(&edited, path, ParseKind::Module);
```

| 問い合わせ | 結果 |
| --- | --- |
| `parse` / `parse_project` | ファイル / package の構文と診断 |
| `module` / `file` / `check` | 指定範囲の semantic result |
| `Database::declaration` | 宣言を含む semantic result |
| `SemanticResult::declaration` | `DeclarationId` の宣言 |
| `definition_at` / `references_to` / `type_at` | 定義・参照・表示型 |
| `all_diagnostics` / `goals` / `outputs` | 診断・ゴール・query 出力 |

位置は絶対パスと UTF-8 byte offset の半開区間。
宣言 ID は module path と名前で、型関連 item は `Type::member` を使う。
`Verified` は検証完了、`Incomplete` は途中結果である。

## 再利用

`read_snapshot` は依存先を含む現在の内容を確認する。
source cache は64 MiB・16,384件、parse・module・query cache は現在と直前の取得世代を保持する。
未変更の問い合わせは失敗結果も同じ `Arc` で再利用する。
`memory_cache_stats` は保持量、`clear_memory` は database の保持を解放する。
呼出側の `Arc` と live arena は別管理である。

package 入力キーは処理系・設定・identity・ソース・manifest・名前付き直接依存から作り、成果物キーに検査範囲を加える。
依存の訪問順や利用側のパスから独立し、共通依存は一度だけ import する。
`force_local` は入口 package または workspace member を再検査し、外部依存は内容の一致する成果物を使う。
LSP の未保存編集も同じ判定を通る。

`artifacts/` の manifest は module 結果、resolver、raw/kernel を別々の `objects/` に参照する。
結果だけで足りる検査では環境を展開せず、後続検査では必要な依存閉包を import する。
全体検査でも、各 package の環境には利用側が参照する module だけを復元する。
小さい依存環境は共有し、大きい成果物だけが保存されている場合は必要な範囲の成果物を作る。
検査済みの小さい依存チェーンは live checker を引き継ぎ、大きい環境と無関係な分岐は解放する。
object は postcard データと種類・codec・長さ・checksum を持ち、native は zstd、WebAssembly は deflate を使う。
破損した環境は再構築し、環境を保存できない場合も結果は保存できる。

`checkpoints/` は依存参照・現在の package の状態・検査順と再開位置を保持する。
`checkpoint_interval` は module 完了時の保存間隔で、既定30秒、ゼロは各境界を対象とする。
保存コストの約10倍以上の検査時間を空け、環境成果物を公開できたら checkpoint を回収する。

公開・pin・GC は store lock と lease で調停し、利用中の成果物と依存閉包を保護する。
supervisor は worker 間で lease を共有し、終了プロセスの lease は OS lock で判定する。
budget は既定8 GiB、`set_cache_budget` で変更できる。
古い未使用 manifest・checkpoint と参照のない object を回収する。

`cache_store_stats` は I/O、再利用・再開、保存失敗、圧縮・展開、回収量を返す。
`retained_bytes_is_upper_bound` の間は保持量が保守的な累積値で、GC が実サイズへ更新する。
supervisor の snapshot・batch 構成は容量集計から除く。
処理系 fingerprint は関連ソース・build script・依存解決・toolchain・target・feature・cfg を追跡し、テスト専用部分を除く。

`progress` は終了時の module 別時間、`progress_events` は依存グラフ・処理段階・開始と完了・checkpoint 保存を通知する。
生成スコープは元のソース module にまとめ、再利用した module も完了数に含める。
実装は [artifact_store.rs](src/artifact_store.rs)、[memory.rs](src/memory.rs)、[build.rs](build.rs)、検証は [tests](tests) を参照。
