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
| `--parse-only` | 構文解析と外部 module・package の読み込み |
| `--no-cache` | 永続キャッシュを読み書きせず全体を検証 |
| `--full-check` | 全体を再検証し、検証済みの結果でキャッシュを更新 |
| `--cache-dir PATH` | キャッシュ保存先を変更 |
| `--clear-cache` | 保存先の中身を削除してから処理 |
| `--cache-stats` | 解析・検査・再利用・保存の件数を表示 |
| `--stats` | raw / kernel のノード数などを表示 |
| `--trace` | 実際の検証を行い、型検査・登録・簡約のログを表示 |
| `--diagnostics compact` / `detailed` | 診断の詳しさを指定 |

キャッシュの仕組みと API は [sema](sema/README.md) を参照。

## 診断と計測

ログと診断は標準エラー、query の結果は標準出力に書く。
診断にはファイル位置、局所文脈、要求された型と制約を表示する。
`#0` は最も内側の束縛を指す。
`_` は推論する穴、`_0` などは宣言内で共有する穴、`?` は解決後も診断を返す確認用のゴールである。

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
ライブラリの計測は [測定記録](../doc/performance-library-checks.md) を参照。

## 処理系のテスト

```sh
cargo test --workspace --locked
cargo clippy --workspace --all-targets --locked -- -D warnings
```

`src/cli/tests/ref_files.rs` が `tests/ok`、`tests/ng` と library project を検査する。
失敗 fixture は `/* expect-error: 診断に含まれる文字列 */` で期待する診断を指定する。
依存クレートを取得済みの場合は Cargo のコマンドに `--offline` を追加できる。
