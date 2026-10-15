# Semantic API とキャッシュ

`sema::Database` は immutable な `SourceSnapshot` から検査結果を計算する。
CLI と LSP が同じ API を利用する。
`sema` は [project](../project/README.md#source-snapshot) の `SourceSnapshot` を再公開する。
crate ごとの役割は [言語処理系](../../doc/book/src/language/implementation.md) を参照。
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

`read_snapshot` は現在のファイル内容を確認し、一致する immutable なテキストと digest を source cache から再利用する。
source cache は64 MiB・16,384件を上限に直近2回の取得世代を保持し、snapshot の未保存編集では変更したテキストだけが新しい digest を持つ。
parse cache はファイル identity・内容・解析方式、module の結果は source と依存関係をキーにする。
未変更の問い合わせは同じ `Arc<SemanticResult>` を返し、失敗結果も実行中に再利用する。
parse・module result・query result は現在と直前の問い合わせで利用した世代を保持する。
`memory_cache_stats` は保持する件数・ソース byte 数・圧縮環境 byte 数を返し、呼出側が持つ `Arc` と検査中の arena はこの集計から独立する。
`clear_memory` は database の保持結果を解放し、既に返した `Arc` は引き続き利用できる。

package の入力キーは、処理系・設定・package identity・自身のソース集合と manifest・名前付き直接依存の入力キーから作る。
成果物のキーには検査範囲も含め、同じ入力と必要範囲を覆う成果物を再利用する。
依存の訪問順や別の利用側のパスは依存 package の入力キーに含まれない。
保存用 ID と読み込み先の ID の対応は resolver・raw・kernel の import API で確定し、共通依存は一度登録する。

保存先の `v2/artifacts/` に成果物 manifest、`v2/objects/` に内容 digest で識別する immutable object を置く。
結果は module ごと、resolver と raw/kernel の export はそれぞれ独立した object とする。
object は種類・codec・格納長・展開長・checksum を持ち、postcard の構造化データを native では zstd、WebAssembly では deflate で圧縮する。
要求範囲が検証済みなら manifest と結果 object だけを読み、環境 object の読み込み・展開を省く。
package の manifest で足りない範囲は、現在の module key に一致する検証済みの個別結果で補完する。
後続 package の検査では依存閉包だけを import し、破損した環境は現在の入力から再構築する。
展開上限を超える環境を保存できない場合も、結果 object は独立に保存できる。
単独ファイルと module 増分検査の結果・環境も同じ object store を使う。

`v2/checkpoints/` の途中再開記録は、依存成果物への参照と現在の package の作業状態・解決済みの検査順・次の位置を持つ。
`CheckOptions::checkpoint_interval` はソース module 完了時の保存間隔の下限で、既定30秒、ゼロは全境界を対象とする。
保存コストの約10倍以上の検査時間を空けるように間隔を調整する。
環境を含む成果物の公開に成功すると、対応する途中再開記録を回収する。
結果だけを保存した場合は、最後に成功した途中再開記録を保持する。
単独ファイルの途中環境は検査順と依存関係を照合し、module 単位の増分検査に利用する。

writer は同期済み object を公開してから manifest を原子的に公開する。
manifest の取得と pin、公開、回収は store lock で調停し、lease は読み込み中の成果物・依存閉包・object を保護する。
CLI supervisor は分割 worker 間で同じ lease を保持し、worker 強制終了後も公開済み checkpoint を保護する。
終了したプロセスの lease は OS の advisory lock で判定して回収する。
ディスク budget の既定は8 GiBで、`Database::set_cache_budget` または `--cache-budget-mib` で変更する。
古い未使用 manifest・checkpoint を回収し、最後の参照がなくなった共有 object を削除する。
利用中の成果物により budget を超える場合は `budget_excess_bytes` に記録し、session 終了後に回収する。
既知の旧形式のキャッシュも回収対象になる。

`cache_store_stats` は結果と環境の読込・書込 byte 数、hit・import・再開、欠損・形式違い・破損・サイズ上限・保存失敗、圧縮・展開時間、共有 object と回収量を返す。
`retained_bytes` は保存先の保持量で、`retained_bytes_is_upper_bound` が真の間は、置換前の記録などを保守的に含む累積会計値を示す。
GC はファイルのサイズを集計し直して、この値を更新する。
保存失敗の理由は `last_save_error` に残し、検証結果は変更しない。
成果物の直列化では、失敗した層とbyte・要素数・深さの上限、メモリ確保失敗を区別して報告する。
処理系 fingerprint は関連 crate・build script・依存解決・toolchain・target・feature・cfg を追跡する。
テスト専用ファイルと examples は分離し、実装内の `cfg(test)` item は Rust AST から除いて計算する。
実装は [artifact_store.rs](src/artifact_store.rs)、[memory.rs](src/memory.rs)、[build.rs](build.rs) を参照。

通常検査と `Database::read_snapshot` は、到達する path dependency の現在のソース内容を確認する。
`CheckOptions::force_local` は入口 package、または workspace の member とルート package を再検査し、現在の外部依存の入力と一致する成果物を再利用する。
CLI は workspace の member 間で同じ `refcache/` を使い、member 単独の検査でも同じ依存成果物を読み込む。
LSP の未保存 buffer も immutable snapshot の入力として同じ再利用判定を通る。

`CheckOptions::progress` は処理終了時に、子 module を含むソース module ごとの検査・省略と所要時間を通知する。
`CheckOptions::progress_events` は選択したソース module とその依存先のグラフ、処理段階、module の検査開始・完了、クエリの成功・失敗を順次通知する。
グラフにはパッケージのルート module も含め、生成した内部スコープは元のソース module にまとめる。
キャッシュで省略した module の完了も通知し、検査後の解析情報の収集・キャッシュ保存は別の処理段階で示す。

## 検証

[semantic API のテスト](tests/semantic.rs) は編集、依存変更、位置情報、永続化と破損時の再構築を確認する。

```sh
cargo test -p sema --locked
```
