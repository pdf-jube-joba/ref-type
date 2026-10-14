# CLI の acceptance test

`python3 tests/tests.py` は Markdown に記述したソースを一時ディレクトリに展開し、CLI を別プロセスで実行する。
Python 3.11 以降の標準ライブラリを使う。
テストの合否は CLI の公開仕様で決まり、処理系を書き直しても同じ文書を実行できる。

```sh
cargo build -p cli --locked
python3 tests/tests.py
python3 tests/tests.py tests/cache --keep-failed
python3 tests/tests.py --filter application_inference
python3 tests/tests.py --list
python3 tests/tests.py --command '/path/to/checker'
python3 -m unittest discover -s tests -p 'test_*.py'
```

`--command` は引数を含むコマンドを指定できる。
ランナーはコマンドを引数列として直接起動する。
テストの文書やディレクトリを位置引数で選択でき、`--filter` はケース名の部分一致または glob で絞り込む。
`--keep-failed` は失敗した一時ディレクトリを残し、その場所を表示する。
`logs/` に各手順のコマンド、作業ディレクトリ、標準出力、標準エラー、JSON レポートが残る。
通常の検査は実行ごとに30秒を上限とし、文書の `timeout` または CLI の `--timeout` で変更できる。

## ケース

一つの文書には、同じ論点について受理と拒否の条件を比較する複数のケースを置く。
本文には、その条件で合否が決まる理由を書く。
ケースは独立したソースディレクトリと空のキャッシュで実行する。

````markdown
## 恒等関数

引数の証明が結果の命題を証明するため受理される。

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

````markdown
```toml case
id = "import"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Base;
\module Use;
```

```ref file=src/Base.ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

```ref file=src/Use.ref
\import \root.Base[] \as B;
\definition P: \Prop := B.P;
```
````

manifest は `toml file=ref.toml`、その他の内容は `text file=...` で記述できる。
`entry` はソースディレクトリからの入力パスで、module では `root.ref`、package と workspace では `.` が既定値である。
`cwd` は同じソースディレクトリからの作業ディレクトリで、既定値は `.` である。
`args` と `env` で検査時の CLI 引数と環境変数を指定する。

## シナリオ

シナリオはソースディレクトリとキャッシュを維持し、各手順を別プロセスで実行する。
`scenario` の直後に書いたファイルを初期状態とし、各 `step` のファイルはその実行前に置き換える。
各手順の設定はシナリオの設定を引き継ぎ、その手順で上書きできる。
`args` は配列全体を置き換え、`env` は変数ごとに上書きする。
前の手順だけに指定した設定は次の手順に引き継がれない。

````markdown
```toml scenario
id = "source-change"
scope = "module"
```

### 初回

命題として正しい式なので受理される。

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

### 再検査

同じソースの検証結果を再利用する。

```toml step
id = "warm"
expect = "accept"
cache = "reused"
```

### 変更

集合を命題として定義するため拒否される。

```toml step
id = "changed"
expect = "reject"
```

```ref
\definition P: \Prop := \Set;
```
````

`remove = ["src/Base.ref"]` は指定したファイルやディレクトリを実行前に削除する。
`cache_dir` は一時ディレクトリからのキャッシュ保存先で、既定値は `cache` である。
`cache_dir = "default"` は CLI の既定の保存先を使う。
保存先を切り替えると、複数の独立したキャッシュを一つのシナリオで比較できる。

`cache = "reused"` と `cache = "unused"` は JSON レポートの `cache.verification_reused` を検査する。
これは永続化された検証結果を使って検証処理を省略したことを表す。
構文解析だけの再利用は含まない。
`--no-cache`、`--full-check`、`--trace` では以前の検証結果を利用しない。

## 観測する結果

ランナーは `--report-json PATH` を各実行に付ける。

```json
{
  "version": 1,
  "outcome": "accepted",
  "cache": {
    "verification_reused": true
  }
}
```

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

## 検査する論点

| 文書 | 主な内容 |
| --- | --- |
| `syntax/` | 字句、括弧、構文と意味の境界 |
| `language/` | sort、証明、帰納型、宣言、Program、macro、型推論 |
| `packages/` | module 間の参照、親子関係、外部ファイル、package の依存 |
| `workspaces/` | member の列挙と検査範囲 |
| `cli/` | 選択、構文のみの検査、query の出力 |
| `cache/` | 再利用、ソース変更、依存変更、workspace の共有 |

数学的な定義と証明は [libs](../libs/README.md) に置く。
[test_cli.py](test_cli.py) は、小さな独立したソースで計測ログの出力、キャッシュ保存先への変更、端末の表示と割り込みを確認する。
Rust の内部状態、保存形式の破損、supervisor のプロセス管理は `src/` の実装テストで検査する。
