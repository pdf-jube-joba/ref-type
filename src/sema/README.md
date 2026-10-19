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
依存の訪問順や利用側のパスから独立するため、別の利用側でも同じ package の検証結果を再利用する。
`force_local` は入口 package または workspace member を再検査し、外部依存は内容の一致する結果を使う。
LSP の未保存編集も同じ判定を通る。

`artifacts/` の manifest は module ごとの検証結果を `objects/` に参照する。
結果だけで足りる問い合わせでは型検査環境を展開せずに回答する。
検査の続きには、resolver・raw/kernel・完了ステップを一緒に保持した prefix を使う。
一つの環境を丸ごと復元することで、その環境の内部 ID と共有 DAG を保持する。
prefix の保存バイト列には実行時のハッシュ表の列挙順が反映され、検証結果の object と入力キーは別に保持する。
prefix は読み込んだ package 入力・名前解決したソース範囲・検査済み範囲・追加順を記録し、現在の入力と必要範囲に合うものを選ぶ。
利用側で必要になる宣言が名前解決済みの範囲を超える場合は、その選択で環境を構築する。
環境の構築時は名前解決と型検査を必要な依存閉包に絞り、同じ環境で処理できる依存先と利用側をまとめる。
同じ要求の中ですでに検証した範囲は live 環境に引き継ぎ、独立して選択された package の間でも共通の宣言を共有する。
小さい保存状態は、必要範囲より広い検査済み範囲を含んでいても共有する。
広い環境を使った worker がメモリ上限に達した場合は、必要範囲だけの環境で再試行し、その選択を分割のヒントとともに保存する。
共通依存までの prefix と利用側の検証結果を別々に保存する。

object は postcard データと種類・codec・長さ・checksum を持ち、native は zstd、WebAssembly は deflate を使う。
prefix の検査ステップと入力を照合し、破損した環境は再構築する。
環境を保存できない場合も検証結果を保存できる。

`checkpoints/` は検査中の prefix を保持する。
`checkpoint_interval` は module 完了時の保存間隔で、既定30秒、ゼロは各境界を対象とする。
保存コストの約10倍以上の検査時間を空け、検証結果を公開したら checkpoint を回収する。
再開時も強制検査の指定を確認し、検査途中の状態は checkpoint として扱う。

公開・pin・GC は store lock と lease で調停し、利用中の成果物と依存閉包を保護する。
supervisor は worker 間で lease を共有し、終了プロセスの lease は OS lock で判定する。
保存量は既定では制限せず、必要な場合は `set_cache_budget` で上限を指定できる。
古い未使用 manifest・checkpoint と参照のない object を回収する。

`cache_store_stats` は I/O、再利用・再開、保存失敗、圧縮・展開、回収量を返す。
`retained_bytes_is_upper_bound` の間は保持量が保守的な累積値で、GC が実サイズへ更新する。
supervisor の snapshot・batch 構成は容量集計から除く。
処理系 fingerprint は関連ソース・build script・依存解決・toolchain・target・feature・cfg を追跡し、テスト専用部分を除く。

`progress` は終了時の module 別時間、`progress_events` は依存グラフ・処理段階・開始と完了・checkpoint 保存を通知する。
生成スコープは元のソース module にまとめ、再利用した module も完了数に含める。
実装は [artifact_store.rs](src/artifact_store.rs)、[memory.rs](src/memory.rs)、[build.rs](build.rs)、検証は [tests](tests) を参照。
