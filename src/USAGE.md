# 利用方法

リポジトリのルートで実行する。

```sh
cargo run -p cli -- libs/std
cargo run -p cli -- libs
cargo run -p cli -- libs/std --module std.Data.Nat --diagnostics compact
```

入力は package・workspace のディレクトリ、またはルート module を置いた `.ref` ファイル。
package の入口は `src/root.ref`、依存先は `ref.toml` で指定する。

```toml
[package]
name = "example"
[dependencies]
std = { path = "../std" }
```

共通の親ディレクトリに workspace を置ける。

```toml
[workspace]
packages = ["std", "algebra/basic", "algebra/module_theory"]
```

workspace 入力は全 member と依存先を検査し、`[package]` もある場合はルート package を含める。
一つの member はそのディレクトリを入力にするか、`--module` に package 名を指定する。
外部 module と import は [表面構文](../doc/book/src/language/syntax.md#2-module)、配置は [libs](../libs/README.md) を参照。

## 検査とキャッシュ

workspace の member は、ソースファイルからの実行でも workspace 直下の `refcache/` を共有する。
workspace 外は入力ディレクトリ、単独ファイルは親ディレクトリに保存する。
`--cache-dir` はこの既定値より優先する。

| オプション | 動作 |
| --- | --- |
| `--module NAME` | 指定した module・子 module と、その参照先の宣言を検証 |
| `--module-only` | `--module` で指定した module 自身と参照先を検証 |
| `--list-modules` | ソース module の検査用パスを一行ずつ表示 |
| `--memory-mib N` | Linux で仮想メモリを制限。既定3072 MiB、0は起動時の上限を維持 |
| `--batch-seconds N` | Linux のパッケージ検査で大きな範囲を分割するまでの秒数。既定180、末端の検査には適用しない |
| `--parse-only` | 構文解析と外部 module・package の読み込み |
| `--no-cache` | 選択した範囲を永続キャッシュの読み書きなしで検証 |
| `--full-check` | 選択した範囲を再検証し、検証済みの結果でキャッシュを更新 |
| `--full-check-local` | 入口パッケージ、または workspace の各パッケージの選択範囲を再検証し、外部依存のキャッシュを再利用 |
| `--no-progress` | 進捗バーと所要時間の表示を抑制 |
| `--progress-tty` | ログ出力先と別に、制御端末 (`/dev/tty`) に進捗バーを表示 |
| `--cache-dir PATH` | キャッシュ保存先を変更 |
| `--cache-budget-mib N` | ディスクの保持上限 MiB。既定8192、利用中の成果物は保護 |
| `--clear-cache` | 保存先の中身を削除してから処理 |
| `--cache-stats` | 解析・検査・再利用・保存の件数を表示 |
| `--report-json PATH` | 合否と永続的な検証結果の再利用を JSON で保存 |
| `--checkpoint-seconds N` | package途中のcheckpoint保存間隔。既定30秒、0は毎module完了時 |
| `--stats` | raw / kernel のノード数などを表示 |
| `--trace` | 実際の検証を行い、型検査・登録・簡約のログを表示 |
| `--diagnostics compact` / `detailed` | 診断の詳しさを指定 |

`--module` を省略すると入口と読み込んだ全依存の全 module を検査する。
指定すると、その module・子 module と参照先に絞る。
`--module-only` は自身と参照先に絞り、同名 module は `--list-modules` の `Name#2` などで区別する。
`--full-check-local` は検査範囲を変えず、入口 package または workspace member の再検査を強制する。
依存の現在の内容は通常検査でも確認する。

Linux の package 検査は、親 supervisor が一つずつ worker を起動する。
大きな範囲が時間・メモリ上限に達すると、親自身の宣言と各子 module に分割する。
末端は時間で打ち切らず、メモリ制限と Ctrl+C を維持する。
全 worker は固定した source snapshot と実行内の成果物を共有し、ソースが変わると再実行を求める。

キャッシュは処理系・設定・ソース・manifest・依存入力・検査範囲を照合する。
無変更なら結果を再利用し、後続 package の検査には依存環境を復元する。
module 完了境界の checkpoint から途中再開でき、保存コストの約10倍以上を空けて次を保存する。
`--full-check` と入口の `--full-check-local` は再開を省いて再検査する。
budget 超過時は利用中の成果物と依存を保護し、未使用の成果物を回収する。
保存形式と API は [sema](sema/README.md#再利用) を参照。

`--cache-stats` は query・I/O・圧縮・復元・保存失敗・回収量を表示する。
`environment_hits` は環境復元数、`restored_modules` はその省略数、`package_hits` は package 成果物の再利用数である。
`checkpoint_hits`・`checkpoint_writes`・`checkpoint_skips` は途中再開の件数、`budget_excess_bytes` は利用中データによる容量超過を表す。
`retained_bytes_is_upper_bound` の間は保持量が保守的な累積値で、GC が実サイズへ更新する。

端末には進捗・完了数・現在の module・経過時間と package 別の `check` / `skip` 件数を表示する。
総数は選択範囲と依存先のソース module 数で、キャッシュ省略も完了に含める。
リダイレクト時やログ有効時は module 別の所要時間を標準エラーへ出し、`--progress-tty` で制御端末に進捗も表示できる。
各 module の時間は自身の解析・展開・検査・保存を含み、子と依存は別に計上する。
`shared = total - 各 module の時間合計` であり、共通準備・checkpoint・解放などを含む。
`total` は CLI 内の処理時間で、Cargo のビルドと起動時間は含めない。

## 診断と計測

診断・ログは標準エラー、query 結果は標準出力へ書く。
診断には位置・局所文脈・要求型・制約を表示し、`#0` は最内の束縛を表す。
`_` は推論する穴、`_0` などは宣言内で共有する穴、`?` は解決済みでも失敗を返す確認用ゴールである。
簡潔な診断は最初のエラーで停止する。

```sh
RUST_LOG=ref_type::typing=debug cargo run -p cli -- libs/std --full-check
RUST_LOG=ref_type::reduction=trace cargo run -p cli -- libs/std --full-check
REF_TYPE_PROFILE_DECLARATIONS=fieldMulAssocNN cargo run -p cli -- libs/std --no-cache
```

`RUST_LOG` は `--trace` の既定フィルタより優先する。

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
`REF_TYPE_COMPACT_DIAGNOSTICS=1` でも簡潔な診断を選べるが、CLI の指定が優先する。
`REF_TYPE_PROFILE_COSTS` は `resolve.,namespace.,kernel.` のような接頭辞でも絞れる。
`inclusive_us` は子を含み、`exclusive_us` は計測した子の時間を差し引く。
再帰の内訳は `cost_group` の exclusive 時間で比較する。

`resolve.total` / `resolve.package` は名前解決と展開、`namespace.*` は具体化・再利用判定を測る。
`namespace.translation-failed.*` は比較用の変換失敗数で、最初の原因を `translation-failure sample=...` に出す。
`query.environment-plan` は検査順・依存情報から checkpoint キーを作る時間である。

途中ログの `event=start` は開始、`completed` と `package_completed` は完了数である。
`event=complete` の `module_seconds` は途中の累積値で、終了時の解析情報収集・保存を含む最終集計とは異なる。
checkpoint 保存時は `event=checkpoint-saved` を出す。

詳細計測・資源制限・中断後のログ分析は [benchmarks](../benchmarks/README.md) を使う。

```sh
cargo build -p cli --locked
REF_TYPE_PROFILE_PROGRESS=1 REF_TYPE_PROFILE_DECLARATIONS=1 \
  python3 benchmarks/bench.py run libs/algebra/homological/computations \
  --cache-mode cold --seconds 180 --memory-mib 3072 --progress-seconds 15 \
  --output benchmarks/runs/check/report.json
```

`--cache-mode cold` は空の専用キャッシュを作り、保存処理も計測する。
最大 RSS は子孫を含む個々のプロセスの最大値である。

## 処理系のテスト

```sh
cargo build -p cli --locked
python3 tests/tests.py
cargo test --workspace --locked
python3 -m unittest discover -s tests -p 'test_*.py'
cargo clippy --workspace --all-targets --locked -- -D warnings
```

[受け入れテスト](../tests/README.md) は Markdown のソースと編集手順を CLI で実行する。
`--report-json` の `outcome` と終了コードは `accepted` / 0、`rejected` / 1、`internal-error` / 2。
`cache.verification_reused` は永続的な検証結果による検査省略を表す。
依存取得済みなら Cargo に `--offline` を追加できる。
