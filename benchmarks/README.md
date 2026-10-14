# 計測とログ分析

Python の入口は `bench.py` にまとめている。
Linux と Python 3.11 以降の標準ライブラリを使う。
計測するバイナリは事前にビルドし、計測は順番に実行する。

```sh
cargo build -p cli --release --locked
python3 benchmarks/bench.py run libs/std --binary target/release/cli --runs 3
python3 benchmarks/bench.py libraries --binary target/release/cli
python3 benchmarks/bench.py cache --binary target/release/cli --checkpoint
python3 benchmarks/bench.py analyze benchmarks/run-logs/000-libs-std.log
python3 benchmarks/tests.py
```

| サブコマンド | 用途 |
| --- | --- |
| `run` | 指定した入力を繰り返して計測 |
| `libraries` | package や workspace の依存先を先に計測 |
| `cache` | chain・diamond・編集・依存順の変更を含む生成 workload の計測 |
| `analyze` | 完了したログと中断したログの分析 |

`libraries` の入力を省略すると、`libs/ref.toml` に列挙した package とその依存先を計測する。
利用例を計測する場合は `libraries libs/category` のように入力を指定する。
同じ package に複数の経路から依存していても一度だけ列挙する。

## キャッシュと繰り返し

`run` の既定は `--cache-mode off` で、CLI に `--no-cache` を渡す。
`--cache-mode cold` は各実行に空の一時キャッシュを用意し、保存処理も計測する。
`--cache-dir` を指定すると、指定したディレクトリのキャッシュを実行間で共有する。
`libraries` は既定で `refcache/library-check/` を共有する。

```sh
python3 benchmarks/bench.py run libs/std --runs 3 --cache-mode cold
python3 benchmarks/bench.py run libs/std --runs 2 --cache-dir refcache/std-measurement
python3 benchmarks/bench.py run libs/algebra/homological/concrete_complexes \
  --module concrete_complexes.Field.Tensor --runs 3 --cache-mode cold \
  --seconds 600 --batch-seconds 600 --memory-mib 3584
```

`cache` は深さを指定できる package の chain と、二つの経路が同じ package に依存する diamond を生成する。
無変更検査、別の利用側、入口編集、推移依存編集、依存順変更、独立した依存の追加を順に計測する。
`--checkpoint` は CLI が checkpoint の保存を報告した時点で中断し、同じ保存先からの再開と再検査を計測する。
一時ソースと一時キャッシュは `refcache/benchmark-scratch/` に作り、終了時に削除する。
`--work-dir` で一時領域、`--depth` で chain の深さを指定できる。

## レポートと資源制限

`--output` は JSON レポートの保存先で、既定は `benchmarks/<サブコマンド>.json` である。
各実行のログと CLI レポートは、その隣の `<名前>-logs/` に保存する。
実行を繰り返した場合は入力ごとの中央値と最大 RSS も集計する。
JSON は各実行の終了後に原子的に更新し、中断までの結果を残す。

各実行には wall time、user time、system time、最大 RSS、終了状態、ソースの digest、保存量を記録する。
CLI の公開レポートから合否と検証結果の再利用を取得する。
検査に失敗した入力や、実行中に変更されたソースは完了した計測として集計しない。
バイナリが実行全体を通して同じ内容であることも確認する。

| オプション | 既定値と用途 |
| --- | --- |
| `--seconds` | 300秒。各実行の時間上限 |
| `--memory-mib` | 3072 MiB。各プロセスの仮想メモリ上限 |
| `--cache-mib` | 8192 MiB。CLI のキャッシュ容量設定 |
| `--output-mib` | 8 MiB。各実行のログ容量上限 |
| `--batch-seconds` | CLI が検査範囲を分割するまでの秒数 |
| `--progress-seconds` | 30秒。実行中の経過時間を表示する間隔 |

中断や上限到達では supervisor に終了を通知して子プロセスの回収を待ち、終了しない場合は強制終了する。
最大 RSS は `wait4` が返す、子孫を含む個々のプロセスの最大値である。
同時点のプロセス全体のメモリ合計ではない。

## 詳細計測

`--profile-costs` と `--profile-phases` で詳細計測を有効にする。
呼び出し回数と時間を複数の worker のログから集計し、phase の順序も保存する。
環境変数で指定した `REF_TYPE_PROFILE_*` も使える。

```sh
python3 benchmarks/bench.py run libs/algebra/homological/concrete_complexes \
  --module concrete_complexes.Field.Tensor --cache-mode cold \
  --profile-costs --profile-phases --output benchmarks/tensor-profile.json
python3 benchmarks/bench.py analyze benchmarks/tensor-profile-logs/000-examples-homological-algebra.log \
  --output benchmarks/tensor-analysis.json
```

`analyze` は処理中の宣言、完了した宣言の時間、module の完了時間、phase の経過時間、cost の集計を返す。
詳細計測には追加の処理時間がかかるため、通常の実行の繰り返しと別に計測する。

resolver のような別のプログラムは `--command` で計測できる。
この場合は入力パスだけをコマンドに追加し、CLI 固有の引数は付けない。
追加の引数は末尾の `--extra` に続けて指定する。

```sh
cargo build --manifest-path benchmarks/Cargo.toml --bin resolve-bench --locked
python3 benchmarks/bench.py run libs/geometry/differential_forms \
  --command benchmarks/target/debug/resolve-bench --profile-costs --profile-phases
```

[namespace-results.json](namespace-results.json) と [cache-artifacts.md](cache-artifacts.md) は、各時点の条件と計測記録を保持している。
