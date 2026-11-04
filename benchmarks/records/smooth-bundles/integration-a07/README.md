# A07 統合後の B07 検査

PR #71 を含む main `0eb04199d9470eb2bfbd0757192aeedfc99fd9e1` を B07 ブランチへ取り込んだ。
固定した検査対象コミットは `1bf8a696538cab0a864ff81031e268578d6d4017`。
統合前の B07 HEAD は `da1262271a69dd062226f93f6793adbc23a60976`。
B07 パッケージのツリーは `961dd9d5d908ef3fedfaa0f060afd67a2a3a5100` のままで、実・複素の native な滑らかな枠束作用と局所微分同相を含む全ソースを保持した。
A07 の `fourier_l2` も main とバイト単位で一致する。
競合はロードマップの総件数・見積もり行だけで、未完了の計画リンクを再集計した 72 件・378 千行に整合させ、A07・B07 双方の完了記録と登録を保持した。

## Checker と固定入力

`source /workspace/.ref-type-tools/activate.sh && cargo build -p cli --release --locked --offline` は終了コード 0、1m 05s。
checker の SHA256 は `e522fa32bb5fd5c74b077ec43108c80e7049694872d2373cc34bc50fe342d4d2` で、統合前の B07 検査と同じである。
Rust と検査ドライバのソースは取り込んだ main と一致する。
16 GiB の cgroup と 4 CPU の環境で同時 worker は 1 個、通常検査のキャッシュ上限は 16384 MiB、対象・回帰の仮想メモリ上限は 10240 MiB、全体検査は 12288 MiB とした。
既存のキャッシュを保持し、通常のソース・依存照合で検証した結果を再利用する。

各 scope で開始・終了のソース snapshot、対象一覧、checker の同一性をドライバが確認した。
さらに snapshot の全ファイルを、固定コミットの Git blob と現在の checkout にバイト単位で照合した。
対象・回帰の全ソースおよび alias は、全体検査 snapshot の対応部分とも一致した。
後続の証跡コミットは数学ソースと検査入力を変更しない。

## 結果

| Scope | 確認済み | 新規 | 再利用 | 終了コード | 保存失敗 | 破損読み込み | worker 復旧 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| smooth_bundles | 3524 | 0 | 3524 | 0 | 0 | 0 | 0 |
| normal_bundles | 1685 | 0 | 1685 | 0 | 0 | 0 | 0 |
| fourier_l2 | 2363 | 79 | 2284 | 0 | 0 | 0 | 0 |
| repository | 11914 | 0 | 11914 | 0 | 0 | 0 | 0 |

すべてのドライバと個々の CLI 実行が終了コード 0 で受理された。
各 scope の件数には依存を含み、個々の CLI 実行間では対象が重複する。

| Scope | 秒 | 最大 RSS (KiB) | 最大仮想メモリ (KiB) | lost steps | backend checkpoint resume |
| --- | ---: | ---: | ---: | ---: | ---: |
| smooth_bundles | 51.986 | 618560 | 1069160 | 0 | 0 |
| normal_bundles | 17.912 | 309304 | 1069060 | 0 | 0 |
| fourier_l2 | 55.005 | 1471096 | 1599712 | 0 | 1 |
| repository | 331.479 | 1410856 | 2117836 | 0 | 0 |

## 証跡

[verification.json](verification.json) に正確な命令、コミット、checker・ソース・対象一覧・生レポートの SHA256、終了コード、資源とキャッシュ統計を保存した。
`*-report.json.gz` は各ドライバの完全な報告、`*-attempts.json.gz` は全 CLI の終了コードと execution・storage 統計を含む。
`source-sha256.json.gz` は全体検査の全入力ファイルと SHA256、`aliases.json.gz` は対応する alias である。
ビルドと各ドライバのログも `*.log.gz` に保存した。

生 snapshot・対象一覧・個々の CLI ログと報告は実行環境の次の場所に保持している。

- `work/b07-integration-target/20261104T230744.875418Z` (smooth_bundles)。
- `work/b07-integration-regression/20261104T230841.655526Z` (normal_bundles)。
- `work/b07-integration-fourier/20261104T230903.087617Z` (fourier_l2)。
- `work/b07-integration-full/20261104T231008.503714Z` (repository)。
