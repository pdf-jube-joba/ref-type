# ベンチマーク

Python の入口は `bench.py` で、Linux と Python 3.11 以降の標準ライブラリを使う。
計測するバイナリは事前にビルドし、計測は順番に実行する。

## ケースを選ぶ

[cases.toml](cases.toml) に各ケースの目的、入力、計測対象と既定の資源制限をまとめている。
資源制限は CLI オプションで上書きできる。

```sh
python3 benchmarks/bench.py list
cargo build -p cli --release --locked
python3 benchmarks/bench.py case shared-bodies --binary target/release/cli --runs 3

cargo build --manifest-path benchmarks/Cargo.toml --bin resolve-bench --locked
python3 benchmarks/bench.py case nested-projections
python3 benchmarks/tests.py
```

## その他の入力と生成 workload

| サブコマンド | 用途 |
| --- | --- |
| `run PATH...` | 指定した入力の繰り返し計測 |
| `libraries PATH...` | package または workspace の依存先を先に計測 |
| `cache` | chain・diamond・編集・依存順の変更を含む生成 workload |
| `analyze LOG` | 完了したログと中断したログの分析 |

```sh
python3 benchmarks/bench.py cache --binary target/release/cli --depth 8
python3 benchmarks/bench.py run benchmarks/inputs/shared-bodies.ref --runs 3
python3 benchmarks/bench.py libraries libs/category --binary target/release/cli
python3 benchmarks/scaling.py --binary target/release/cli --depths 8 16 32 64
python3 benchmarks/large_scale.py --binary target/release/cli --sizes 16 32 64 --runs 3
```

`libraries` の入力を省略すると、`libs/ref.toml` の package とその依存先を列挙する。
同じ package に複数の経路から依存していても一度だけ計測する。

`cache` は無変更検査、別の利用側、入口編集、推移依存編集、依存順変更、独立した依存の追加を順に計測する。
checkpointの保存先を使用不能にした場合の診断と、保存先を修復した後の検査も確認する。
`--checkpoint` は保存報告後の中断・再開・無変更検査と、worker の強制終了からの自動復旧を追加する。

`scaling.py` は各 package の宣言数を固定し、依存チェーンの深さだけを変えて空のキャッシュから計測する。
`--width` は各 package の宣言数、`--force` は `--full-check` を指定する。

`large_scale.py` は依存チェーン、共通依存の利用側、namespace の幅、import 数、局所文脈での import、独立した宣言群を個別に増やす。
`--axes` で対象を選び、`--resident-mib` で式ページの常駐予算を指定する。

`large_scale_suite.py` は個別選択の3回計測、3072 / 8192 MiBでの全体検査、再利用、規模変更、復旧を順番に実行する。
`--baseline` を指定すると同じ個別選択と、600秒を上限にした旧方式の全体検査を追加する。
ビルド済みのバイナリを指定し、実行する項目は `--stages`、全体検査と再利用の入力は `--packages` で選べる。

```sh
python3 benchmarks/large_scale_suite.py --binary target/debug/cli --baseline benchmarks/runs/baseline-cli
```

`resolve-bench PATH --retention` はpackageごとに名前解決し、検査済み入力の解放を模擬してresolverの保持量を測る。
ソース構文木を保持した状態と解放した状態を分け、LinuxではRSSと仮想メモリを出力する。
system allocatorを使い、GNU環境では未使用ページを返してから観測する。
このモードは型検査を行わず、CLIの完走計測とは分けて使う。

## 出力とキャッシュ

レポートの既定の保存先は、名前付きケースでは `runs/<ケース名>/report.json`、その他の計測では `runs/<サブコマンド>/report.json` である。
`--output` でレポートの保存先を指定でき、各実行のログと CLI レポートは、その隣の `<名前>-logs/` に保存する。
比較結果の JSON・条件・考察は [records](records/README.md) に保存する。

`run` と `case` の既定は `--cache-mode off` で、checker の計測では CLI に `--no-cache` を渡す。
`--cache-mode cold` は各実行に空の一時キャッシュを用意し、保存処理も計測する。
`--cache-mode shared` はレポートの隣の `cache/` を実行間で共有し、`--cache-dir` で別の保存先を指定できる。
`libraries` は既定で共有キャッシュを使う。
一時ソースと一時キャッシュは `runs/scratch/` に作り、終了時に削除する。
`--work-dir` で一時領域を指定できる。

JSON は各実行の終了後に原子的に更新し、中断までの結果を残す。
wall time、user time、system time、最大 RSS、終了状態、ソースの digest、保存量、公開レポートの合否と再利用を記録する。
成功した計測から入力ごとの中央値と最大 RSS を集計する。
ソースやバイナリが途中で変わった計測は、完了した計測として扱わない。

## 資源制限と詳細分析

| オプション | 名前付きケース以外の既定値と用途 |
| --- | --- |
| `--seconds` | 300秒。各実行の時間上限 |
| `--memory-mib` | 3072 MiB。各プロセスの仮想メモリ上限 |
| `--cache-mib` | 省略時は無制限。CLI のキャッシュ容量設定 |
| `--output-mib` | 8 MiB。各実行のログ容量上限 |
| `--batch-seconds` | 比較用の旧 CLI に渡す、検査範囲を分割するまでの秒数 |
| `--progress-seconds` | 30秒。実行中の経過時間を表示する間隔 |

中断や上限到達では supervisor に終了を通知し、子プロセスの回収を待ってから必要なら強制終了する。
最大 RSS は `wait4` が返す、子孫を含む個々のプロセスの最大値である。
同時点のプロセス全体のメモリ合計ではない。

```sh
python3 benchmarks/bench.py case shared-bodies --profile-costs --profile-phases
python3 benchmarks/bench.py analyze benchmarks/runs/shared-bodies/report-logs/000-shared-bodies.log
```

`--profile-costs` と `--profile-phases` は、複数の worker の呼び出し回数と時間を集計し、phase の順序も記録する。
環境変数で指定した `REF_TYPE_PROFILE_*` も使える。
`analyze` は処理中の宣言、完了した宣言と module の時間、phase の経過時間、cost の集計を返す。
詳細計測には追加の処理時間がかかるため、通常の繰り返しと別に計測する。

別のプログラムは `--command` で指定する。
入力パスだけをコマンドに追加し、追加の引数は末尾の `--extra` に続けて指定する。
大きな割当の追跡には [alloc_trace.c](tools/alloc_trace.c) を使える。
