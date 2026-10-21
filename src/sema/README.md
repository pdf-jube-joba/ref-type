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
検査セッションは `Database` が保持する resolver・raw/kernel・完了台帳を所有する。
ソースの module ID と子の索引を先に予約し、要求された本文を必要時に名前解決する。
名前解決の引数環境は差分と置換の共有 DAG で保持し、実際の参照で必要な値を展開する。
検査に渡す名前・import の表も共有し、要求追加時は変更した package の構文木と新しい宣言を追加する。
検査完了後は kernel 側の型・本体と、今後の構造展開・マクロ展開に必要なテンプレートを残し、完了ステップの検査入力を解放する。
依存閉包に含まれる宣言をキューへ追加し、完了したステップは後続の package 要求や検査範囲の拡張で省略する。
参照位置と module ごとの解析結果は共有し、呼出側が保持する結果は過去の snapshot に結び付く。
入力・処理系・設定・強制検査範囲を照合し、以前のセッションと保存成果物の再利用を判定する。
`--full-check` の worker は空の保存領域から新しい検証世代を開始し、その実行内で完了した宣言を共有する。

保存したセッションは package 入力・名前解決したソース範囲・検査済み範囲・追加順を記録する。
checkpoint は resolver と raw の索引、完了ステップ、式グラフのページ参照を結び付ける。
resolver の名前表、引数環境、参照経路、名前空間の対応表は共有 DAG として保存し、復元後も共有を維持する。
セッション情報も16〜128 KiBの内容依存の区切りで保存し、同じ内容の object を再利用する。
復元は保存オブジェクトを順次読み、直列化データ全体の展開用バッファを持たない。
kernel の本文は必要なページだけを読み込み、保存時も確定したページの object を再利用する。
依存全体の本文を一度に展開せず、同じ内部 ID で後続の検査を続ける。
package 完了時の索引保存は、前回の保存位置から検査ステップ数が倍増した境界と、外部依存の完了境界、要求全体の完了時に行う。
索引の符号化範囲はその時点のセッション全体だが、package ごとに増大する prefix を毎回保存する累積費用を抑える。

object は postcard データと種類・codec・長さ・checksum を持ち、native は zstd、WebAssembly は deflate を使う。
prefix の検査ステップと入力を照合し、破損した環境は再構築する。
環境を保存できない場合も検証結果を保存できる。

`checkpoints/` は検査中の prefix を保持する。
依存先を検査している間も、checkpoint は実行中の要求のキーで公開し、その要求の復旧で完了台帳を引き継ぐ。
キーは入力と要求範囲全体から作り、個別 package のキャッシュヒットや訪問順から独立させる。
完了した環境の保存時も同じ再開先を更新し、より古い中断 checkpoint が選ばれることを防ぐ。
`checkpoint_interval` は module 完了時の保存間隔で、既定30秒、ゼロは各境界を対象とする。
保存コストの約10倍以上の検査時間を空け、検証結果を公開したら checkpoint を回収する。
メモリ圧迫が続く場合もキャッシュの回収は直ちに行い、検査中のcheckpointには前回の保存コストに応じた間隔を適用する。
再開時も強制検査の指定を確認し、検査途中の状態は checkpoint として扱う。

公開・pin・GC は store lock と lease で調停し、利用中の成果物と依存閉包を保護する。
supervisor は worker 間で lease を共有し、終了プロセスの lease は OS lock で判定する。
保存量は既定では制限せず、必要な場合は `set_cache_budget` で上限を指定できる。
古い未使用 manifest・checkpoint と参照のない object を回収する。

`cache_store_stats` は I/O、再利用・再開、保存失敗、圧縮・展開、回収量を返す。
`retained_bytes_is_upper_bound` の間は保持量が保守的な累積値で、GC が実サイズへ更新する。
supervisor の source snapshot と一時的な通信ファイルは容量集計から除く。
処理系 fingerprint は関連ソース・build script・依存解決・toolchain・target・feature・cfg を追跡し、テスト専用部分を除く。

`progress` は終了時の module 別時間、`progress_events` は依存グラフ・処理段階・宣言と module の完了・checkpoint 保存と保存失敗・保存統計を通知する。
`QueryStats::session` は具体化件数、名前空間・置換表・宣言セルの件数と、式ストアの保持量を返す。
生成スコープは元のソース module にまとめ、再利用した module も完了数に含める。
実装は [artifact_store.rs](src/artifact_store.rs)、[memory.rs](src/memory.rs)、[build.rs](build.rs)、検証は [tests](tests) を参照。
