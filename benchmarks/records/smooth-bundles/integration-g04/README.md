# A07・G04 main 統合後の B07 検査

G04 の PR #73 と A07 の PR #71 を含む main `3e9a3854e242f380349024ad5fca7cb09dad0e63` を取り込んだ。
固定した検査対象コミットは `4e1910e072076d83307851fd7a84b8fabb008eca`、統合前の B07 HEAD は `004123221d538b658370529c963154b19e3fc383`。
取り込み時の競合はなかった。
B07 パッケージのツリーは `961dd9d5d908ef3fedfaa0f060afd67a2a3a5100` のままで、枠束の滑らかな作用・局所微分同相を含む全ソースを保持した。
A07 の `fourier_l2` と G04 の `manifold_gluing` は、取り込んだ main とバイト単位で一致する。
後続コミットは検査証跡と文書の集計を更新し、検査した数学ソース・manifest・checker を保持する。

## Checker と固定入力

`source /workspace/.ref-type-tools/activate.sh && cargo build -p cli --release --locked --offline` は終了コード 0、1m 05s。
checker SHA256 は `e522fa32bb5fd5c74b077ec43108c80e7049694872d2373cc34bc50fe342d4d2`。
Rust と検査ドライバは取り込んだ main と同じである。
16 GiB cgroup、4 CPU、同時 worker 1 個、cache 上限 16384 MiB の環境で通常検査した。
B07・normal_bundles・fourier_l2 の仮想メモリ上限は 10240 MiB、manifold_gluing と全体検査は 12288 MiB。
共有キャッシュを保持し、ソースと依存を照合した通常の検査結果を再利用した。

各 scope の開始・終了 snapshot はバイト単位で一致し、ドライバは対象一覧と checker の同一性も完了時に確認した。
全入力を固定コミットの Git blob および checkout と照合し、対象・回帰のソースと alias は全体検査の対応部分と一致した。
全体検査の入力は 11,426 ファイルである。

## 結果

| Scope | 確認済み | 新規 | 再利用 | 終了コード | 保存失敗 | 破損読み込み | worker 復旧 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smooth_bundles | 3524 | 0 | 3524 | 0 | 0 | 0 | 0 |
| normal_bundles | 1685 | 0 | 1685 | 0 | 0 | 0 | 0 |
| fourier_l2 | 2363 | 0 | 2363 | 0 | 0 | 0 | 0 |
| manifold_gluing | 3155 | 948 | 2207 | 0 | 0 | 0 | 0 |
| repository | 12714 | 0 | 12714 | 0 | 0 | 0 | 0 |

すべてのドライバと個々の CLI 実行が終了コード 0 で受理された。
各 scope は依存を含み、個々の CLI 実行の対象は重複する。

| Scope | 秒 | 最大 RSS (KiB) | 最大仮想メモリ (KiB) | lost steps | backend checkpoint resume |
| --- | ---: | ---: | ---: | ---: | ---: |
| smooth_bundles | 50.868 | 618500 | 1069160 | 0 | 0 |
| normal_bundles | 27.470 | 495312 | 1069060 | 0 | 0 |
| fourier_l2 | 31.123 | 508260 | 1069028 | 0 | 0 |
| manifold_gluing | 106.317 | 2102368 | 2383780 | 0 | 1 |
| repository | 309.209 | 1462300 | 2118128 | 0 | 0 |

## 原本を保持する証跡

[verification.json](verification.json) に、正確な命令・対象コミット・checker・終了コード・資源統計と、全保存物の圧縮前後の SHA256 を記録する。
`*-report.json.gz`、`*-source.json.gz`、`*-targets.json.gz`、`*.log.gz` は原本のバイト列をそのまま gzip 圧縮したものである。
JSON の再シリアライズはしておらず、各 `report_archive.uncompressed_sha256` は同じ scope の `raw_report_sha256` と一致する。
source snapshot と対象一覧も展開した原本の SHA256 を各記録と直接照合できる。

`*-cli-reports.tar.gz` は、その scope の個々の CLI 報告を原本バイト列のまま保存する。
`*-attempts.json.gz` は派生した集計で、各 `archive_member` が対応する tar 内の原本を指し、`raw_report_sha256` がその原本のハッシュである。
集計の execution・storage 統計も対応する原本の値と照合した。
過去の A07 統合記録で使った JSON 再シリアライズ形式とは区別している。

これらの保存物から、報告・入力 snapshot・対象一覧・個別 CLI 原本・ログのハッシュを実行環境に依存せず計算できる。
検査実行そのものの再現には、対象コミットの checkout と通常 checker が必要である。

生の記録も実行環境の次の場所に保持する。

- `work/b07-g04-target/20261104T234139.732018Z` (smooth_bundles)。
- `work/b07-g04-normal/20261104T234255.083827Z` (normal_bundles)。
- `work/b07-g04-fourier/20261104T234322.599689Z` (fourier_l2)。
- `work/b07-g04-gluing/20261104T234353.771964Z` (manifold_gluing)。
- `work/b07-g04-full/20261104T234540.137332Z` (repository)。
