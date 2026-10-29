## このリポジトリについて
proof checker を作る。
**コンパイルすることは忘れて** 単に形式的な記述をチェックするための言語を作る。
余裕があったら proof assistant にする。

\(\text{x} x\)

## 構成
- doc/ はドキュメント置き場
    - doc/book/ に考えている体系についての文章を書く
- formalization/ は他の定理証明支援系による形式化の設計メモ
- src/ は実装

## AI 向け
このファイルには何も追記しないでください。

## リポジトリ全体の通常検査

Linux と Python 3.11 以降で、リポジトリのルートから実行する。

```sh
cargo build -p cli --release --locked && python3 scripts/check_all.py
```

`libs` の全 module と依存先を列挙し、開始時のソースを固定して順番に通常検査する。
処理系・ソース・依存・検査範囲が一致する検証済みキャッシュは再利用する。
パッケージごとの子プロセスでメモリを解放し、上限に達した範囲は自身と子 module に分割して続行する。
各子プロセス内でも、新しい checkpoint があれば自動で再開する。
分割できない範囲だけは設定した最大メモリまで段階的に再試行し、それでも進展がなくなった場合は非ゼロ終了する。

```sh
python3 scripts/check_all.py --initial-memory-mib 3072 --memory-mib 6144 --cache-budget-mib 12288 --min-free-mib 256
python3 scripts/check_all.py --state-dir work/repository-check --cache-dir libs/refcache
```

`--memory-mib` は各 CLI プロセスに許す最大の仮想メモリ上限で、RSS やコンテナのメモリ上限とは別である。
通常の子プロセスは `--initial-memory-mib`（既定 3072 MiB）と最大値の小さい方で開始する。
チェックポイント再開と範囲分割を先に試し、分割できない範囲だけ上限を倍増して最大値（既定 6144 MiB）まで再試行する。
この最大値を超える再試行はしない。
最大値 0 は初期上限での分割後に既存の OS 上限で一度だけ試す指定である。
対象列挙は最初から最大値を使う。
現在の 16 GiB コンテナでは単一 worker で検証している。
別の環境では CLI supervisor、ドライバ、OS の余裕も含めて最大値を指定する。
`--cache-budget-mib` は利用中の成果物を保護した上でのキャッシュ回収目標であり、必要な保存量を必ず収める上限ではない。
`--min-free-mib` はログとキャッシュの保存先に確保する空き容量の目安である。
`--time-limit-seconds` で呼び出し全体の検査時間を制限できる。

`work/repository-check/latest.json` は最新のレポートを指す。
実行ごとのディレクトリには開始時の `source.json`、全対象の `targets.json`、各処理のログと JSON、集計した `report.json` が残る。
型検査の拒否、保存失敗、メモリ・時間制限、中断を個別の処理レポートで区別する。
集計には新規検査・再利用の対象、最大 RSS・仮想メモリ、保存失敗数を記録する。
最大値は CLI の監視値と worker の終了時統計で、同時点の全プロセスの合計とは異なる。

終了コード 0 は、開始時に列挙した全対象の通常検査が確認され、保存失敗がなく、終了時にもソース・対象一覧・処理系が一致した場合だけ返す。
ドライバの失敗は 2、中断は 130 である。
失敗や中断後は同じコマンドを実行すると、現在のソースに適合するキャッシュと checkpoint を検証して再開する。
前回の集計ファイルだけを根拠に検査を省略することはない。
同じソースと処理系で前回成功していれば、まず全体の通常キャッシュ検証を試し、必要に応じてパッケージ単位に戻る。
`verified-state.json` はこの実行順の選択だけに使い、成功判定には使わない。

小規模な動作確認は `python3 scripts/test_check_all.py`、中断・worker 復旧の確認は `python3 benchmarks/bench.py cache --binary target/release/cli --checkpoint` で実行できる。
CLI の詳細は [利用方法](src/USAGE.md)、計測方法は [benchmarks](benchmarks/README.md) を参照。
