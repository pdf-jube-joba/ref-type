# A07 固定ソースの検査記録

数学ソースの検査対象は `6e07dfd89d5ff54f7d117c77593ac25859774d14`、base は `ed1af945bfdfdc1849bf1919317e3ce422b1ac1f`。
以後のコミットは公開 API・計画の Markdown と検査証跡のみを変更し、検査した `.ref`、manifest、checker のソースを保持する。
全10,492ファイルのソースを checkout と検査対象コミットのバイト列に照合し、対象検査・依存回帰のソースと alias が全体検査の snapshot と一致することを確認した。
全体検査の開始・終了 snapshot と対象一覧も一致した。

通常 release checker を `cargo build -p cli --release --locked` でビルドし、終了コード0を確認した。
Rust・Cargo は1.99.1で、checker の SHA-256 は `d9666f0c81134c54ba4ece0fc658d8034fe7337de9d3e7845a0c0c7e9c6aa4ec`。
checker のソースは base commit と同一であり、全検査の開始・終了でもバイナリが一致した。

通常全体検査は11,729対象すべてを受理した。
新規11,337・再利用392、保存失敗0、破損読み取り0、全体の終了コード0。
100回の外側の CLI 実行もすべて終了コード0である。
最後の既存パッケージ `compact_support_k` では285,212,688 bytesのメモリ割当失敗後、checkpoint 35685から同一ソースで自動再開した。
この実行はworker 2個・回復1回・backend checkpoint resume 1回で、全対象の受理を確認した。
CLI の進行統計には `lost_steps = 3202`、重複・replay済み source stepsは各0が記録されている。
全体ドライバの `checkpoint_resumes = 0` はchecking側の別カウンタであり、backend側の再開は個別報告の `storage.checkpoint_resumes = 1` に記録される。
復旧前後の報告とログを `compact-support-recovery.json.gz`・`compact-support-recovery.log.gz` に保存した。

| 検査 | 対象と依存の受理 | ソースから検査 | 再利用 | 終了コード |
| --- | ---: | ---: | ---: | ---: |
| `focused` | 992 | 0 | 992 | 0 |
| `local` | 992 | 22 | 970 | 0 |
| `fourier_schwartz` | 865 | 9 | 856 | 0 |
| `lp_spaces` | 870 | 458 | 412 | 0 |
| `complex_hilbert` | 343 | 165 | 178 | 0 |

`local` は A07 の全22モジュールを `--full-check-local` で再検査し、依存970モジュールを再利用した結果である。
これらの対象検査と依存回帰はすべて保存失敗0・破損読み取り0・worker回復0。
16 GiB cgroupで、全体検査の初期・最大上限は12 GiB、対象検査は8 GiB、ソース再検査と依存回帰は6 GiBに制限した。
全体のworker最大RSSは10,336,800 KiB、最大仮想メモリは12,424,604 KiB。
キャッシュを保持し、通常のソース・依存照合を使用した。

[verification.json](verification.json) に、正確な命令・対象コミット・checker・終了コード・資源・キャッシュ統計を記録する。
`repository.json.gz` は全体報告、`attempts.json.gz` は各実行の集計、`targets.json.gz` は全対象一覧、`source-sha256.json.gz` と `aliases.json.gz` は全ソースと alias の対応である。
`checker-source-sha256.json.gz`、対象・回帰報告、ビルド・全体ドライバのログも同梱する。

ロードマップの完了手順に従い、成果と検査結果を [fourier_l2 README](../../../libs/analysis/fourier_l2/README.md) に移した。
A09・A18 の A07 依存リンクを公開 README へ置き換え、A07 を完了欄へ移して個別計画ファイルを削除した。
