# CLI の acceptance test

`python3 tests/tests.py` は Markdown に記述したソースを一時ディレクトリに展開し、CLI を別プロセスで実行する。
Python 3.11 以降の標準ライブラリを使う。

```sh
cargo build -p cli --locked
python3 tests/tests.py
python3 tests/tests.py tests/cli --keep-failed
python3 tests/tests.py --filter application_inference
python3 tests/tests.py --list
python3 tests/tests.py --command '/path/to/checker'
```

`--command` は引数を含むコマンドを指定できる。
ランナーはコマンドを引数列として直接起動する。
テストの文書やディレクトリを位置引数で選択でき、`--filter` はケース名の部分一致または glob で絞り込む。
`--keep-failed` は失敗した一時ディレクトリを残し、その場所を表示する。
`logs/` に各手順のコマンド、作業ディレクトリ、標準出力、標準エラー、JSON レポートが残る。
通常の検査は実行ごとに30秒を上限とし、文書の `timeout` または CLI の `--timeout` で変更できる。

## ケース

同じ論点の受理・拒否条件を一つの文書で比較し、本文に理由を書く。
ケースは独立したソースディレクトリで実行する。

````markdown
## 恒等関数

引数の証明が結果の命題を証明する。

```toml case
id = "identity"
scope = "module"
expect = "accept"
```

```ref
\definition identity(P: \Prop)(p: P): P := p;
```
````

`scope = "module"` のソースは module の本文として記述する。
ランナーは `root.ref` に外部 module の宣言を生成し、その本文を `Test.ref` に保存する。
module 名と parameter が必要な場合は次のように指定する。

```toml
name = "Identity"
parameters = '''A: \Set, a: A'''
```

`scope = "package"` と `scope = "workspace"` は、コードブロックに書いたファイルを相対パスに展開する。
package の manifest を省略した場合は、名前が `test` の package を生成する。

ファイル配置の例は [imports.md](packages/imports.md) を参照。

manifest は `toml file=ref.toml`、その他の内容は `text file=...` で記述できる。
`entry` はソースディレクトリからの入力パスで、module では `root.ref`、package と workspace では `.` が既定値である。
`cwd` は同じソースディレクトリからの作業ディレクトリで、既定値は `.` である。
`args` と `env` で検査時の CLI 引数と環境変数を指定する。

## シナリオ

シナリオはソースディレクトリを維持し、各手順を別プロセスで実行する。
`scenario` の直後に書いたファイルを初期状態とし、各 `step` のファイルはその実行前に置き換える。
各手順の設定はシナリオの設定を引き継ぎ、その手順で上書きできる。
`args` は配列全体を置き換え、`env` は変数ごとに上書きする。
前の手順だけに指定した設定は次の手順に引き継がれない。

````markdown
```toml scenario
id = "source-change"
scope = "module"
```

```toml step
id = "before"
expect = "accept"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

```toml step
id = "after"
expect = "accept"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P;
```
````

`remove = ["src/Base.ref"]` は指定したファイルやディレクトリを実行前に削除する。

## 観測する結果

ランナーは `--report-json PATH` を各実行に付ける。

| `expect` | レポートの `outcome` | 終了コード |
| --- | --- | --- |
| `accept` | `accepted` | 0 |
| `reject` | `rejected` | 1 |

`internal-error`、クラッシュ、タイムアウト、レポートの欠落、終了コードとの不一致は実行の失敗として扱う。
CLI の内部異常の終了コードは2である。
不明な設定、重複した ID、閉じていないフェンス、ソースのないケースは文書のエラーとして扱う。

query の結果や出力先を検査する場合は、次の設定を追加できる。

| 設定 | 検査する内容 |
| --- | --- |
| `stdout` | 標準出力全体との一致 |
| `stdout_same_as` | 同じシナリオの先行する手順の標準出力との一致 |
| `stdout_lines` | 標準出力の行数 |
| `stdout_bytes_min` | 標準出力の最小バイト数 |
| `stderr_empty` | 標準エラーが空かどうか |

大量の出力を検査する場合は、`ref repeat=10000` で小さなソースを反復して展開できる。

### 出力の部分一致・順序・集計

`checks` は標準出力・標準エラー・制御端末の出力を照合する。
正規表現は各行の先頭・末尾に `^`・`$` が一致する方式で評価する。

```toml
checks = [
  { stream = "stderr", contains = ["event=planned"], absent = ["\r"] },
  { stream = "stderr", ordered = ["event=start", "event=complete"] },
  { stream = "stderr", pattern = 'event=finished success=true', count = 1 },
]
```

| 設定 | 検査する内容 |
| --- | --- |
| `stream` | `stdout`、`stderr`、`terminal` のいずれか |
| `contains` | 含まれる文字列の配列 |
| `absent` | 含まれない文字列の配列 |
| `ordered` | 指定した順に現れる文字列の配列 |
| `pattern` | 一致する正規表現 |
| `count` | 正規表現の一致数、省略すると一回以上 |
| `sum_equals` | `pattern` の数値の合計と比較する正規表現 |
| `relative_tolerance` | 合計の比較で許容する相対誤差、既定はゼロ |
| `positive` | 比較する合計が正の数であること |

`sum_equals` を使う場合、両方の正規表現に数値を取り出すキャプチャを一つずつ設ける。
比較先は一回だけ一致し、各数値は有限の非負数である必要がある。
[計測の例](cli/profiling.md)を参照。

### 制御端末と割り込み

`terminal = true` は擬似端末を制御端末として CLI を起動する。
標準出力と標準エラーは別々のログファイルに保存し、制御端末への出力は `checks` の `terminal` で照合する。
端末のログも `logs/` に保存する。
この実行方式には Unix の擬似端末が必要である。

```toml
terminal = true
expect = "interrupted"
interrupt = { terminal = "\u001b[2K", stderr = "checking " }
```

`interrupt` に指定した文字列がすべて観測できたら、制御端末へ Ctrl+C を送る。
`expect = "interrupted"` は Ctrl+C の送信と SIGINT による終了を検査し、JSON レポートを要求しない。
割り込み前の終了やタイムアウトは失敗となる。
[端末の例](cli/terminal.md)を参照。

数学の定義・証明は [libs](../libs/README.md)、内部状態・保存形式・プロセス管理は Rust のテストで検査する。
