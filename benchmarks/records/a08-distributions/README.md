# A08 分布の検査記録

数学ソースのコミットは `7b3d31318916120347f02afdfc78c40ef36c1f3e`、base は `d2232bb8ec5ff43feb2323477c8815b10ee309a8`。
この記録を追加するコミットは数学ソースを変更しない。
検査後に main `60c8e1551` を取り込んだ `d8dc48f6a8b01dd5e7e2dd42edfc5f230b8144b4` も、数学ソースと処理系ソースは検査コミットと一致する。
2026-11-12 UTC に通常のキャッシュ付き release checker で検査した。

`cargo build -p cli --release --locked` は終了コード0。
rustc 1.99.1、cargo 1.99.1 を使用し、checker SHA-256 は `915f17d4d0720b8165e1dd521df1a033265365e5bfa085a069e8fad93cdbda22`。
保存間隔の指定を守る処理系の修正を含む。既存のチェックポイント回帰テスト13件も全て受理した。
`cadence-tests.log` にその出力を保存する。

| 対象 | 受理した依存閉包 | ソースから検査した module | 終了コード |
| --- | ---: | ---: | ---: |
| `focused` | 1,611 | 1,611 | 0 |
| `lp` | 870 | 568 | 0 |
| `change` | 1,543 | 123 | 0 |
| `partitions` | 581 | 419 | 0 |

`focused` は新規121 module 全体を含む `distributions` の検査である。
`lp`、`change`、`partitions` はそれぞれ `lp_spaces`、`change_of_variables`、`smooth_partitions` の全体と依存閉包を検査する。
対象・回帰は全て保存失敗0である。
ソースと依存が一致する検証済みキャッシュを通常の方法で再利用した。

初回12 GiB全体検査は既存の `k_theory_thom.Thom.Complexification.Compact.Isomorphism` でメモリ上限に達した（13,283対象受理）。
数学ソースを変更せず、通常キャッシュの再開を行った。
旧checkerではメモリ上限と保存エラーがあり、保存間隔の自動的な増大が回復を遅くしていた。
間隔の指定を守る最小修正の後、15 GiB上限・保存間隔120秒で該当依存を受理した（3,312 verified module、2,908 source-checked module、保存失敗・回復・lost step全て0）。
初回報告と資源回復の履歴も圧縮して保持する。

全体検査は 13,915 対象を受理し、終了コード0。
新規 12,645、再利用 1,270、CLI 実行 105 回。
保存失敗 0、破損キャッシュ読み取り 0、worker 回復 0、checkpoint 再開 0。
worker 最大 RSS は 11,481,596 KiB、最大仮想メモリは 14,836,944 KiB。
最終全体検査の初期・最大仮想メモリ上限は15 GiB、対象・回帰は4.5 GiB、キャッシュ予算は16 GiBである。

全 12,607 ソースについて開始時 snapshot、最終 checkout、数学コミットの Git blob を照合した。
全体ドライバは終了時にも snapshot・対象一覧・checker の一致を確認した。

```sh
source /workspace/.ref-type-tools/activate.sh && cargo build -p cli --release --locked
target/release/cli libs/analysis/distributions --module distributions --diagnostics compact --no-progress --memory-mib 4608
REF_TYPE_GRAPH_SPILL_DIR=/tmp python3 scripts/check_all.py --initial-memory-mib 15360 --memory-mib 15360 --cache-budget-mib 16384 --state-dir work/a08-final-check
```

[verification.json](verification.json) は正確な命令、終了コード、コミット、集計、checker と snapshot の hash を記録する。
`repository.json.gz` と `worker-reports.json.gz` は全体と各CLIの報告、`targeted-reports.json.gz` は対象・回帰の報告である。
`targets.json.gz`、`source-sha256.json.gz`、`aliases.json.gz`、`checker-source-sha256.json.gz` が検査範囲とソースの照合情報を持つ。
`resource-history.json.gz` と `a08-resource-*.log.gz` に資源回復の履歴を保存する。
`build.log` と `driver.log.gz` にビルドと全体ドライバの出力を保存する。

Sobolev 比較は Euclid 空間全体、有限実指数 \(1\le p<\infty\)、任意の非負整数次数を扱う。
微分同相の分布引き戻しは任意の開集合間で構成し、滑らかな正則分布との一致を証明する。
平滑化は任意の分布と滑らかなコンパクト台の核に対する定理である。
