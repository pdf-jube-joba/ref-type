# CLI の acceptance test

`python3 tests/tests.py` は Markdown に記述したソースを一時ディレクトリに展開し、CLI を別プロセスで実行する。
Python 3.11 以降の標準ライブラリを使う。

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
`logs/` に各手順のコマンド、作業ディレクトリ、標準出力、標準エラーが残る。
通常の検査は実行ごとに30秒を上限とし、文書の `timeout` または CLI の `--timeout` で変更できる。

## ケース

同じ論点の受理・拒否条件を一つの文書で比較し、本文に理由を書く。
ケースは独立したソースディレクトリと空のキャッシュで実行する。

````markdown
## 恒等関数

引数の証明が結果の命題を証明する。

```toml case
id = "identity"
scope = "module"
expect = "accept"
```

```ref
\definition identity[P: \Prop][p: P]: P := p;
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

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

```toml step
id = "warm"
expect = "accept"
cache = "reused"
```
````

`remove = ["src/Base.ref"]` は指定したファイルやディレクトリを実行前に削除する。
`cache_dir` は一時ディレクトリからのキャッシュ保存先で、既定値は `cache` である。
`cache_dir = "default"` は CLI の既定の保存先を使う。

`cache = "reused"` と `cache = "unused"` を指定した手順では、`--report-json PATH` を付けて JSON レポートの `cache.verification_reused` を検査する。
レポートは `logs/` に保存する。
永続化された検証結果による検査の省略を表し、構文解析だけの再利用は含まない。
`--no-cache`、`--full-check`、`--trace` では以前の検証結果を利用しない。

## 観測する結果

| `expect` | 終了コード |
| --- | --- |
| `accept` | 0 |
| `reject` | 1 |

内部異常の終了コード2、クラッシュ、タイムアウトは実行の失敗として扱う。
不明な設定、重複した ID、閉じていないフェンス、ソースのないケースは文書のエラーとして扱う。

大量の query を実行する場合は、`ref repeat=10000` で小さなソースを反復して展開できる。

### 保存ファイルの比較

`files` はソースディレクトリからの相対パスにあるファイルの構成と内容を記録する。
ディレクトリを指定すると、その配下のファイルを再帰的に記録する。

```toml
files = [{ path = "refcache", same_as = "saved", nonempty = true }]
```

`same_as` は同じパスを記録した先行手順との一致を検査する。
`nonempty` はファイルが一つ以上あるかを検査する。
[ファイル比較の例](cache/files.md)を参照。

数学の定義・証明は [libs](../libs/README.md)、内部状態・保存形式・プロセス管理は Rust のテストで検査する。
[test_runner.py](test_runner.py) は共通ランナーの動作を検査する。
