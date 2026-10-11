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
| `--module-only` | `--module` で指定した module 自身と参照先を検証 |
| `--list-modules` | ソース module の検査用パスを一行ずつ表示 |
| `--memory-mib N` | Linux で仮想メモリを制限。既定3072 MiB、0は起動時の上限を維持 |
| `--parse-only` | 構文解析と外部 module・package の読み込み |
| `--no-cache` | 選択した範囲を永続キャッシュの読み書きなしで検証 |
| `--full-check` | 選択した範囲を再検証し、検証済みの結果でキャッシュを更新 |
| `--full-check-local` | 入口パッケージの選択した範囲を再検証し、依存先は自身のソースと manifest が一致するキャッシュを再利用 |
| `--no-progress` | 進捗バーと所要時間の表示を抑制 |
| `--progress-tty` | ログ出力先と別に、制御端末 (`/dev/tty`) に進捗バーを表示 |
| `--cache-dir PATH` | キャッシュ保存先を変更 |
| `--clear-cache` | 保存先の中身を削除してから処理 |
| `--cache-stats` | 解析・検査・再利用・保存の件数を表示 |
| `--checkpoint-seconds N` | package途中のcheckpoint保存間隔。既定30秒、0は毎module完了時 |
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

全ライブラリの検査には、資源上限に応じて検査範囲を分割する [check_libraries.py](../benchmarks/check_libraries.py) を使える。
実行手順と検査結果の読み方は [ライブラリの型検査](../libs/README.md#型検査) を参照。
通常の CLI も Linux では既定で仮想メモリを3072 MiBに制限し、起動元にさらに小さい制限がある場合はそちらを維持する。
`--module-only` は、親の宣言を検査してから子の各範囲を独立に検査する場合に使う。
名前が繰り返される module は、`--list-modules` が返す `Name#2` などのパスで指定できる。

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
`package_hits` は package 境界の復元で省略した package 数、`package_writes` は保存した package 環境数、`package_skips` はサイズ上限などで保存を省略した境界数である。
具体化した宣言の引数列と置換は、共有する配列を一度だけ保存し、復元後も共有する。
package キャッシュには名前解決の状態も含まれ、依存先が一致すれば利用側の module 追加後も依存環境を再利用する。
検査中の package は、一定時間が経過した後のソース module 完了時に途中環境を `.partial` に保存する。
同じキャッシュ保存先で再実行すると、名前解決の状態と検査位置を復元し、保存位置以降を検査する。
未完了の module が入れ子で存在する場合も、保存した検査順の続きから再開する。
`--checkpoint-seconds` の既定値は30秒で、保存に時間がかかった場合は、その約10倍以上の検査時間を空けて次を保存する。
一つの module の処理中に中断した場合は、最後に保存できた module 境界に戻る。
途中環境にも package と依存先のソース・検査範囲・設定・処理系の照合を行い、`--full-check` と入口 package の `--full-check-local` は再開を省略して検査し直す。
保存は一時ファイルへの書き込み後に置き換えるため、保存途中で停止しても前の checkpoint は残る。
保存サイズ上限を超えた場合は、その package の以後の途中保存を省略し、最後に成功した checkpoint を残す。
`--cache-stats` の `checkpoint_hits`・`checkpoint_writes`・`checkpoint_skips` で途中環境の復元・保存・省略件数を確認できる。
`REF_TYPE_PROFILE_PROGRESS=1` のログでは、保存成功時に `event=checkpoint-saved` を出力する。
異なる入口パッケージ間で共有する場合は、`--cache-dir` に同じ保存先を指定する。

端末では標準エラーの一行を更新し、進捗バー、完了 module 数／総 module 数、現在の module、パッケージ内の完了数と経過秒数を表示する。
検査前に選択範囲の依存グラフを使って総数を決め、キャッシュで省略した module も完了数に含める。
総数にはパッケージ直下の宣言を持つルート module と子 module を含める。
読み込み・依存解析・キャッシュ照合・名前解決・環境復元・検査・保存の段階も表示する。
進捗は module 数を表し、残り時間の推定ではない。
端末の描画は毎秒最大10回に制限する。
標準エラーをファイルへ出力する場合や、`--trace`・`RUST_LOG`・`REF_TYPE_PROFILE_*` によるログを有効にした場合は、module ごとの `check` / `skip` と所要秒数を表示する。
`--progress-tty` を指定すると、これらのログを残しながら制御端末に進捗バーを表示する。
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
| `REF_TYPE_PROFILE_PROGRESS=1` | 処理段階、module の開始・完了、完了数と経過秒数を随時出力 |
| `REF_TYPE_PROFILE_NAMESPACES=1` | import の名前空間と ID 対応表の件数 |
| `REF_TYPE_PROFILE_DIAGNOSTICS=1` | 診断生成・表示の時間と RSS |
| `REF_TYPE_PROFILE_ENVIRONMENTS=1` | checkpoint のキー・復元位置・保存サイズ |
| `REF_TYPE_PROFILE_COSTS=1` | 入れ子の処理ごとの inclusive / exclusive 時間とキャッシュ統計 |
| `REF_TYPE_PROFILE_COSTS_PROGRESS_MS=15000` | cost 計測中の途中経過を出す間隔 |

先頭の三つは `1` で全件、名前の一部で対象を絞る。
`REF_TYPE_PROFILE_COSTS` は `resolve.,namespace.,kernel.` のような接頭辞のカンマ区切りでも対象を選べる。
`inclusive_us` は子の処理を含み、`exclusive_us` は計測した子の時間を差し引く。
再帰呼び出しの inclusive 時間は重複するため、内訳の比較には `cost_group` の exclusive 時間を使う。
`resolve.total` は macro・structure 展開を含む型推論前の名前解決、`namespace.*` は elaboration 中のインスタンス構築・再利用判定である。
package を依存順に追加する経路では、名前解決を `resolve.package` で計測する。
namespace の inclusive 時間には引数の比較で呼ぶ kernel の変換判定が含まれる。
`namespace.compare-arguments` は引数列の比較、`namespace.compare-rigid-arguments` は簡約で変わらない引数による候補の除外、`namespace.compare-syntax`・`namespace.compare-alpha`・`namespace.reduce-alias-head` は比較の各段階を測る。
`namespace.telescope-candidates` は引数列単位で走査した候補数、`definition-exact-hit`・`definition-equivalent-hit`・`definition-origin-hit`・`definition-candidate-hit`・`definition-fresh` は定義の再利用結果を数える。
`namespace.translation-failed.*` は再利用判定用の kernel 項への変換に失敗した回数であり、診断として報告された型エラーの件数とは異なる。
cost 計測中は、その変換で生じた kernel エラーの種類ごとに最初の原因を `namespace.translation-failure sample=...` として出力する。
`query.environment-plan` は検査順と依存情報から checkpoint のキーを作る時間を表す。
`REF_TYPE_COMPACT_DIAGNOSTICS=1` でも簡潔な診断を選べるが、CLI の指定が優先される。
簡潔な診断では最初のエラーで検査を停止する。
時間とメモリの上限を付けた計測には [check.py](../benchmarks/check.py) を使える。
次の実行は空の専用キャッシュを作り、キャッシュ保存を含む初回検査を計測する。

```sh
cargo build -p cli --locked
REF_TYPE_PROFILE_PROGRESS=1 REF_TYPE_PROFILE_DECLARATIONS=1 \
  python3 benchmarks/check.py libs/homological_algebra \
  --cache-dir "$(mktemp -d /tmp/ref-type-profile.XXXXXX)" \
  --seconds 180 --memory-mib 3072 --progress-seconds 15 \
  --log benchmarks/check.log --result benchmarks/check.json
```

`progress` 行と宣言の `checking` 行は処理の途中にも書き出すため、中断後も最後に開始した処理を追える。
`completed` は完了数であり、`event=start` の module の通し番号ではない。
`package_completed` は同じパッケージ内の完了数を表す。
`event=complete` の `module_seconds` はその時点までの累積値で、後続の解析情報収集やキャッシュ保存を含む最終集計とは異なる。
`REF_TYPE_PROFILE_DECLARATIONS` には名前の一部を指定して出力対象を絞れる。
詳細ログをファイルに保存しながら進捗バーを表示する場合は、制御端末のあるシェルから次のように実行する。

```sh
REF_TYPE_PROFILE_PROGRESS=1 REF_TYPE_PROFILE_DECLARATIONS=1 \
  /usr/bin/time -v -o benchmarks/homological-memory.log \
  target/debug/cli libs/homological_algebra --progress-tty \
  --cache-dir "$(mktemp -d /tmp/ref-type-profile.XXXXXX)" \
  > benchmarks/homological.log 2>&1
```

module・宣言の途中ログと完了した宣言の所要時間は `homological.log` に、実行全体の最大 RSS などは `homological-memory.log` に残る。
Ctrl+C で検査を中断でき、中断前に出力された途中ログはファイルに残る。
計測スクリプトは途中の RSS と CPU 時間、終了時の最大 RSS・ユーザー／システム CPU 時間を記録する。
型検査前に package ごとの検査完了順を調べる場合は、resolver の計測用プログラムを使える。

```sh
cargo run -p resolve --example resolve-bench -- libs/homological_algebra --package-order \
  > benchmarks/module-order.log
```

`package_complete` 番目の module と、その完了直後に検査する `next_module` を表示する。
この順序はキャッシュ省略と型エラーからの復旧がない場合の予定であり、実測時間は通常の検査ログで確認する。
既存の測定条件と結果は [results.json](../benchmarks/results.json) にある。

## 処理系のテスト

```sh
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

`src/cli/tests/ref_files.rs` が `tests/ok`、`tests/ng` と library project を検査する。
失敗 fixture は `/* expect-error: 診断に含まれる文字列 */` で期待する診断を指定する。
依存クレートを取得済みの場合は Cargo のコマンドに `--offline` を追加できる。
