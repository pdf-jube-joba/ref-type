# ソースの受理・拒否テスト

`python3 tests/tests.py` は Markdown に記述したソースを一時ディレクトリに展開し、処理系の受理・拒否を検査する。
Python 3.11 以降の標準ライブラリを使う。

```sh
cargo build -p cli --locked
python3 tests/tests.py
python3 tests/tests.py tests/language --keep-failed
python3 tests/tests.py --filter application_inference
python3 tests/tests.py --list
python3 tests/tests.py --command '/path/to/checker'
```

`--command` は引数を含むコマンドを指定できる。
ランナーはコマンドを引数列として直接起動する。
テストの文書やディレクトリを位置引数で選択でき、`--filter` はケース名の部分一致または glob で絞り込む。
`--keep-failed` は失敗した一時ディレクトリを残し、その場所を表示する。
`logs/` に各手順のコマンド、標準出力、標準エラーが残る。
実行ごとの制限時間は30秒で、ランナーの `--timeout` で変更できる。

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

## シナリオ

シナリオはソースディレクトリを維持し、各手順を別プロセスで実行する。
`scenario` の直後に書いたファイルを初期状態とし、各 `step` のファイルはその実行前に置き換える。
各手順の設定はシナリオの設定を引き継ぎ、その手順で上書きできる。
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

期待値は `accept` または `reject` で指定する。
終了コード0を受理、1を拒否として照合する。
それ以外の終了コード、クラッシュ、タイムアウトはテストの失敗として扱う。
不明な設定、重複した ID、閉じていないフェンス、ソースのないケースは文書のエラーとして扱う。

数学の定義・証明は [libs](../libs/README.md) を参照。
