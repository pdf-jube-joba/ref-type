# 実行速度の計測

Rust / Cargo と既存の依存クレートだけで実行できます。リポジトリのルートで次を実行します。

```sh
# 変更前の基準を保存
cargo bench -p cli --bench performance -- --save-baseline before

# 実装を変更してから比較し、変更後の結果も保存
cargo bench -p cli --bench performance -- --baseline before --save-baseline after
```

`cargo bench` が最適化付きで再ビルドしてから測定を開始します。ビルド時間は含みません。
依存関係が手元にある環境では、Cargo の `--offline` も使えます。
通常は全ケースで数分程度かかります。ケース単位の進捗は標準エラー出力へ表示します。

## 計測対象

| ケース名 | 計測する処理 | 計測前に済ませる準備 |
| --- | --- | --- |
| `parse/mccarthy91` | McCarthy 91 の字句解析・構文解析 | ソースはバイナリに埋め込み |
| `load/library` | `lib/root.ref` と外部モジュールの読み込み・構文解析 | なし |
| `check/library` | ライブラリの elaboration・型検査・定義登録 | モジュール読み込み・構文解析 |
| `pipeline/library` | ライブラリの読み込みから elaboration まで | なし |
| `pipeline/mccarthy91` | McCarthy 91 の読み込み・elaboration・評価 | なし |
| `normalize/beta256` | Set/Prop の恒等関数の 256 段の β 簡約 | arena と入力項の構築 |
| `evaluate/countdown32` | Program の `Prun`、パターンマッチ、定義展開による 32 からのカウントダウン | 構文解析・elaboration・入力環境の構築 |
| `evaluate/countdown128` | 同じ計算を 128 から実行 | 同上 |

`pipeline/*` はライブラリ API を同一プロセスから呼びます。CLI の起動、引数解析、
結果の文字列化、端末出力は含みません。`load/*` は OS のファイルキャッシュが
温まった状態の測定で、ディスクの cold-start 性能ではありません。

## 結果の見方

- `median (ms)`: 各サンプルの「計測時間合計 ÷ 反復回数」の中央値。小さいほど高速です。
- `CV (%)`: サンプル平均時間の標準偏差 ÷ 平均 × 100。計測のばらつきの目安です。
- `change (%)`: `(今回の中央値 ÷ 基準の中央値 - 1) × 100`。負なら高速化、正なら低速化です。

既定では各ケースを 200 ms 以上ウォームアップし、20 サンプルを取ります。
各サンプルは準備・後片付けを含む実時間で 50 ms 以上になるまで反復します。
遅いケースは 1 回の実行が 1 サンプルになるので、50 ms は実行時間の上限ではありません。
ウォームアップは最低 1 回実行します。

各反復の arena・環境は新しく作り、反復をまたぐメモリ増加やキャッシュの使い回しを防ぎます。
結果は `black_box` で保持し、結果オブジェクトと入力環境の最終破棄は計測から除外します。
型検査ケースは環境の作成も含み、正規化・評価の単体ケースは入力の準備を除外します。
正規化・カウントダウンの期待結果を検証し、elaboration の失敗や評価の fuel 切れは失敗扱いにします。
ベンチマークでは tracing subscriber を設定しないため、`RUST_LOG` によるログ出力はありません。

小さな差を判断するときは、他のビルドや重い処理を止め、同じマシン・電源設定・Rust バージョン・
ビルド設定・入力で繰り返してください。差分表示は有意差検定ではありません。
基準と今回の TSV のメタデータも確認します。ケース名が同じでも入力を変更すれば別の負荷になるため、
`lib/`、テスト入力、ベンチマーク自体を変えたときは基準を取り直します。

## 対象と計測時間の調整

```sh
# ケース一覧
cargo bench -p cli --bench performance -- --list

# Program の評価だけを比較
cargo bench -p cli --bench performance -- --filter evaluate/ --baseline before

# 動作確認用の短い試走（性能判断には使わない）
cargo bench -p cli --bench performance -- --samples 2 --warmup-ms 0 --sample-ms 1

# ばらつきを確認するために長めに計測
cargo bench -p cli --bench performance -- --filter normalize/ --samples 50 --warmup-ms 1000 --sample-ms 200
```

フィルタは名前の部分一致です。一致するケースがない場合や、基準に比較対象のケースがない場合は
エラーになります。保存名には英数字・`-`・`_` が使えます。既存の基準は上書きしません。

## 保存形式とケースの追加

結果は Git 管理外の `target/benchmarks/<名前>.tsv` に保存されます。
`--output-dir /tmp/ref-type-results` などで保存先を変更できます。
`cargo clean` をまたいで保持したい場合は別の保存先を指定してください。

TSV のコメント行には日時（Unix 秒）、Git commit と作業ツリー状態、Rust バージョン、
OS・CPU 情報、Rust flags、計測設定を記録します。各データ行にはケース名、サンプル番号、
反復回数、計測時間合計（ns）、1 反復あたりの時間（ns）を保存します。
このファイルを表計算ソフトやスクリプトで集計できます。

ケースは [`performance.rs`](performance.rs) の `Case::new` で登録します。
反復関数は、準備を済ませてから `timed` で対象処理を測り、その `Duration` を返します。
正しさの検証はタイマーの外に置き、負荷の大きさを名前に含めます。
計測・比較・保存の共通処理は [`support/mod.rs`](support/mod.rs) にあります。
