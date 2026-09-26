# Semantic API と incremental checker

`front::Database` が source snapshot から parse 結果と semantic result を計算する。
CLI の通常チェックも同じ API を使う。

| crate | 入力と結果 |
| --- | --- |
| `front-syntax` | source text → span を持つ構文、外部 module と package の構成 |
| `elaboration` | module 構文 → 名前解決、macro 展開、型推論、raw IR、kernel による検証、semantic observations |
| `front` | immutable な source snapshot → 依存関係、query cache、永続化できる semantic result |
| `kernel` | 分類済みの項と宣言 → 独立した型検査と登録 |

## API

```rust
use front::{Database, DeclarationId, ParseKind, SourceSnapshot};

let source = SourceSnapshot::read("libs/std")?;
let mut db = Database::with_cache("libs/std/refcache");
let checked = db.check(&source);
assert!(checked.is_success());

let id = DeclarationId {
    module: vec!["std".into(), "Nat".into()],
    name: "Nat".into(),
};
let declaration = db.declaration(&source, &id);

let edited = source.with_file(
    "libs/std/src/Nat.ref",
    std::fs::read_to_string("libs/std/src/Nat.ref").unwrap(),
);
let parsed = db.parse(&edited, "libs/std/src/Nat.ref", ParseKind::Module);
let file = db.file(&edited, "libs/std/src/Nat.ref");
```

`SourceSnapshot::read` は source tree と path dependencies の内容を取り込み、以後の query はその内容を参照する。
`with_file` と `without_file` は元の snapshot を保持したまま編集後の snapshot を作る。
`SourceSnapshot::new` と `insert` を使うと、ファイルシステムに存在しない source も扱える。
ファイルの identity と symlink の対応は読み込み時に固定する。

| 問い合わせ | 結果 |
| --- | --- |
| `Database::parse` | root または外部 module の構文と parse diagnostics |
| `Database::parse_project` | package と外部ファイルを結合した module 構文 |
| `Database::module` / `file` | 対象 module とその依存先の semantic result |
| `Database::declaration` | 宣言の ID、種類、位置、elaboration 後の型表示 |
| `Database::check` | project 全体の semantic result |
| `SemanticResult::definition_at` / `references_to` | 名前解決で確定した参照と宣言位置 |
| `SemanticResult::type_at` | 宣言または参照位置の型表示 |
| `SemanticResult::all_diagnostics` / `goals` | diagnostics、goal の位置・文脈・判断・制約 |

位置はファイルの絶対パスと UTF-8 byte offset の半開区間で表す。
宣言 ID は module path と宣言名で構成し、constructor と associated definition は `Type::member` を名前に使う。
名前参照は解決時の source span を保持し、宣言位置は宣言全体の span を保持する。
型と出力は module の名前を使って表示し、query ごとの arena の割り当て順から独立させる。
module parameter、constructor、record field、associated definition も宣言として取得できる。
同名の module が繰り返される場合、二つ目以降の semantic path に `#2`、`#3` のような出現番号を付ける。
macro template の参照は template の定義位置に記録する。
local binder の文脈は goal に保存する。

型検査が失敗した場合も、その時点までに得た宣言・参照・goal を返し、独立した scope の検査を続ける。
`ModuleStatus::Verified` は kernel の検証を完了した結果を表し、`Incomplete` は失敗時に取得できた途中の情報を表す。
外部 module に parse error がある場合は、その module と依存する module を保留し、独立した module の情報を返す。

## 再利用と依存関係

parse cache はファイルの identity、内容、root と module の解析方式をキーにする。
semantic cache の単位は module で、宣言の変更は所属 module を無効化する。
依存先には親 scope、import 先とその子 module、継承した import alias、macro を公開する scope を含める。
宣言と子 module が混在する scope は宣言順の影響もまとめて扱う。
scope に含まれる module の追加・削除もキーに反映する。

未変更の query は同じ `Arc<SemanticResult>` を返し、goal を含む失敗結果も実行中に再利用する。
一部が変わった場合は、変更された module とその利用者を調べ、必要な依存先を含む module 群を elaboration と kernel 検査に渡す。
この再構築には未変更の依存先も含まれるため、編集対象の依存関係が広い場合は再チェックする範囲も広がる。
処理中の metavariable と constraint は宣言ごとに解放し、raw と kernel の workspace は検査する module 群の処理後に解放する。
`clear_memory` で query と parse の保持結果を解放できる。

## 永続キャッシュ

kernel が検証を完了した module 群から、型・参照・出力などの semantic result を JSON に保存する。
キーには source の構文と位置、依存関係、package manifest、追加設定、checker の実装・依存関係・Rust toolchain・target の fingerprint を含める。
checker の fingerprint は build script が各 crate の Rust source、Cargo manifest、lockfile から生成する。

キャッシュには payload の SHA-256 checksum を付け、一時ファイルからの rename で保存する。
破損・形式の違い・読み込み失敗は cache miss として source から再計算する。
保存に失敗した場合も検証結果を返し、`cache_write_failures` に件数を記録する。
キャッシュはローカルの検査済み結果を再利用するための保存先である。

```sh
cargo run --release --locked --offline -- libs/std --cache-stats
cargo run --release --locked --offline -- libs/std --cache-stats
cargo run --release --locked --offline -- libs/std --no-cache
cargo run --release --locked --offline -- libs/std --full-check
```

CLI は `libs/std` の検査結果を `libs/std/refcache/` に保存し、単独の `.ref` ファイルを指定した場合はその親ディレクトリの `refcache/` に保存する。
`--cache-dir` で保存先を変更できる。
`--full-check` はキャッシュを再利用せず依存先を含む全体を検証し、検証済みの結果でキャッシュを更新する。
`--no-cache` はキャッシュの読み書きを無効にして全体を検証する。
source tree の読み込みでは `refcache/` を除外する。
`--parse-only` は parse と module 読み込みを行う。
`--trace` と `--stats` は実際の検証を実行し、その処理のログと arena の統計を表示する。
`--cache-stats` は parse 件数、再利用件数、検査する module 群の大きさ、disk cache の読み書き件数を表示する。

## 検証

```sh
cargo test --workspace --locked --offline
cargo clippy --workspace --all-targets --locked --offline -- -D warnings
```

semantic API のテストは `tests/semantic.rs` にあり、buffer 編集、依存先・import・macro・manifest の変更、goal、source location、永続化と破損時の再構築を確認する。
CLI の既存 fixtures と library project もこの frontend を通る。

module の部分編集による再利用は、次の example で未編集・再実行・buffer 編集・全再構築を比較できる。

```sh
cargo run --release --locked --offline -p front --example incremental -- libs/std libs/std/src/Algebra/Algebra.ref
```

example は編集後の incremental result と全再構築の semantic result が一致することも確認する。

### 計測例

2026-09-26 に release build の `libs/std` で測定した。
別プロセスの CLI を各３回実行し、stdout の一致も確認した。

| 条件 | 経過時間 | 最大 RSS | 検査対象 module 数 |
| --- | --- | --- | --- |
| 空の disk cache | 2.44–2.84 秒 | 約 201 MiB | 63 |
| 別プロセスの disk cache 再利用 | 0.12–0.14 秒 | 約 55 MiB | 0 |

`incremental` example では、初回 3.13 秒、同じ snapshot への再問い合わせ 57 ms、`Algebra/Algebra.ref` への宣言追加後 1.50 秒だった。
編集後の全再構築は 2.98 秒で、両方の semantic result は一致した。
編集時は 51 ファイル中１ファイルを再解析し、依存先の再構築を含む 38 module を検査した。
