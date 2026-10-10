# 利用方法

コマンドはリポジトリのルートから実行する。

```sh
cargo run -p cli -- libs/std
cargo run -p cli -- tests/ok/eval_id.ref
```

入力は `ref.toml` のあるパッケージディレクトリ、またはルート module を含む `.ref` ファイルである。
パッケージは `src/root.ref` を入口にする。

```toml
[package]
name = "example"

[dependencies]
std = { path = "../std" }
```

外部 module と import の記法は [表面構文](../doc/book/src/language/syntax.md#2-module)、ライブラリの構成は [libs](../libs/README.md) を参照。

## 検査とキャッシュ

通常の検査は入力ディレクトリの `refcache/` を利用する。
単独ファイルの場合は親ディレクトリに保存する。

| オプション | 動作 |
| --- | --- |
| `--module NAME` | 指定した module・子 module と、その参照先の宣言を検証 |
| `--parse-only` | 構文解析と外部 module・package の読み込み |
| `--no-cache` | 選択した範囲を永続キャッシュの読み書きなしで検証 |
| `--full-check` | 選択した範囲を再検証し、検証済みの結果でキャッシュを更新 |
| `--full-check-local` | 入口パッケージの選択した範囲を再検証し、依存先は自身のソースと manifest が一致するキャッシュを再利用 |
| `--no-progress` | 進捗バーと所要時間の表示を抑制 |
| `--cache-dir PATH` | キャッシュ保存先を変更 |
| `--clear-cache` | 保存先の中身を削除してから処理 |
| `--cache-stats` | 解析・検査・再利用・保存の件数を表示 |
| `--stats` | raw / kernel のノード数などを表示 |
| `--trace` | 実際の検証を行い、型検査・登録・簡約のログを表示 |
| `--diagnostics compact` / `detailed` | 診断の詳しさを指定 |

`--module` を省略すると、入口と読み込んだ全依存パッケージの全 module を検査対象にする。
パッケージ全体とその参照先を検査する場合は、`ref.toml` の package 名を module に指定する。
個別の証明を編集する場合は、その module を指定すると、子 module と依存する宣言を含めて検査できる。
`--full-check-local` は再検査とキャッシュ再利用の方針を指定するもので、検査対象の選択には `--module` を使う。

```sh
cargo run -p cli -- libs/std --module std.Data.Nat --diagnostics compact
cargo run -p cli -- libs/differential_forms --module differential_forms --full-check-local --diagnostics compact
```

キャッシュの仕組みと API は [sema](sema/README.md) を参照。

同じコマンドを二度実行すると、別プロセスでのキャッシュ再利用を確認できる。

```sh
cargo run -p cli --release --locked -- libs/std --cache-stats
cargo run -p cli --release --locked -- libs/std --cache-stats
cargo run -p cli --release --locked -- libs/std --no-cache
cargo run -p cli --release --locked -- libs/std --full-check
cargo run -p cli --release --locked -- libs/std --full-check-local
```

`--cache-stats` の `environment_hits` は復元した checkpoint 数、`restored_modules` は復元で検査を省略した module 数、`environment_bytes` は保持中の圧縮 checkpoint の合計サイズである。

端末では標準エラーの一行を更新し、進捗バー、完了 module 数／総 module 数、現在の module、パッケージ内の完了数と経過秒数を表示する。
検査前に選択範囲の依存グラフを使って総数を決め、キャッシュで省略した module も完了数に含める。
総数にはパッケージ直下の宣言を持つルート module と子 module を含める。
読み込み・依存解析・キャッシュ照合・名前解決・環境復元・検査・保存の段階も表示する。
進捗は module 数を表し、残り時間の推定ではない。
標準エラーをファイルへ出力する場合や、`--trace`・`RUST_LOG`・`REF_TYPE_PROFILE_*` によるログを有効にした場合は、module ごとの `check` / `skip` と所要秒数を表示する。
module ごとの秒数は読み込み・構文解析・名前解決と展開・検査・解析情報の収集・検査結果のキャッシュ処理を合計した実測の経過時間であり、処理の終了時に表示する。
子 module や依存 module の時間は、その module 自身に計上する。
生成された内部 module の時間は、元のソース module に計上する。
再利用した module にも、今回実際に行った解析やキャッシュ処理の時間を表示する。
`shared` は `total` から各 module の時間合計を引いた値であり、個別の module に計上していない処理の時間を表す。
ソース全体の読み込み、共通の環境準備、checkpoint の保存・復元、環境の解放などが含まれる。
各 module と `shared` の秒数の合計が `total` に一致するのは、この計算方法によるものであり、独立した計測値同士の一致を確認した結果ではない。
`total` は CLI 内の引数処理から module の計測結果の表示と環境の解放までの時間であり、Cargo のビルド・プロセス起動時間と最後の `shared` / `total` の表示時間は別である。

```sh
cargo run -p cli -- libs/topology --full-check-local
cargo run -p cli -- libs/topology --full-check-local --no-progress
```

`--full-check-local` では、C が B に、B が A に依存するとき、B 自身のソースと manifest をキャッシュに照合する。
一致すれば、A には B の検証時に保存したソースを使い、チェック済みの依存環境を復元する。
B の変更、キャッシュの欠損・破損がある場合は、現在の依存ソースを読み込んで再検証する。
キャッシュは通常の検査と共有し、再検証に成功した結果で更新する。
単独ファイルに指定すると、そのファイルから読み込む module 全体を再検証する。

## 診断と計測

ログと診断は標準エラー、query の結果は標準出力に書く。
診断にはファイル位置、局所文脈、要求された型と制約を表示する。
`#0` は最も内側の束縛を指す。
`_` は推論する穴、`_0` などは宣言内で共有する穴である。
`?` は確認用のゴールであり、解決済みでもゴールを表示して検査を失敗させる。

`RUST_LOG` は `--trace` の既定フィルタより優先する。

```sh
RUST_LOG=ref_type::typing=debug cargo run -p cli -- libs/std --full-check
RUST_LOG=ref_type::reduction=trace cargo run -p cli -- libs/std --full-check
REF_TYPE_PROFILE_DECLARATIONS=fieldMulAssocNN cargo run -p cli -- libs/std --no-cache
```

| 環境変数 | 計測対象 |
| --- | --- |
| `REF_TYPE_PROFILE_DECLARATIONS` | 宣言の検査時間 |
| `REF_TYPE_PROFILE_LOCAL_DEFINITIONS` | 局所定義の検査時間 |
| `REF_TYPE_PROFILE_LOWERING` | kernel 定義への変換・登録時間 |
| `REF_TYPE_PROFILE_PHASES=1` | 各処理段階の時間と RSS |
| `REF_TYPE_PROFILE_MODULES=1` | module の読み込み・具体化・復旧 |
| `REF_TYPE_PROFILE_NAMESPACES=1` | import の名前空間と ID 対応表の件数 |
| `REF_TYPE_PROFILE_DIAGNOSTICS=1` | 診断生成・表示の時間と RSS |
| `REF_TYPE_PROFILE_ENVIRONMENTS=1` | checkpoint のキー・復元位置・保存サイズ |

先頭の三つは `1` で全件、名前の一部で対象を絞る。
`REF_TYPE_COMPACT_DIAGNOSTICS=1` でも簡潔な診断を選べるが、CLI の指定が優先される。
簡潔な診断では最初のエラーで検査を停止する。
時間とメモリの上限を付けた計測には [check.py](../benchmarks/check.py) を使える。
既存の測定条件と結果は [results.json](../benchmarks/results.json) にある。

## 処理系のテスト

```sh
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

`src/cli/tests/ref_files.rs` が `tests/ok`、`tests/ng` と library project を検査する。
失敗 fixture は `/* expect-error: 診断に含まれる文字列 */` で期待する診断を指定する。
依存クレートを取得済みの場合は Cargo のコマンドに `--offline` を追加できる。
