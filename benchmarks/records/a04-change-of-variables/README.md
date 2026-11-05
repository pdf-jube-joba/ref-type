# A04 固定ソースの検査記録

数学ソースは `a54156d6bade9d94c214b490e7f35629294b4f50`、統合 base は `a38cc89135fbe5bbcd62e4bb6b82b2c476b71cbc`。
B07・G04 がマージされた main 上で、実装・公開 API・計画の完了処理を固定して検査した。
以後のコミットは検査証跡と README のみを変更する。

通常 release checker を `cargo build -p cli --release --locked` でビルドし、終了コード0を確認した。
rustc 1.99.1 (58cf8f9c3 2026-10-13)、cargo 1.99.1 (5f94df478 2026-08-27)。
checker SHA-256 は `d0c6b9183fbb40a0aec74a4573995ab425404966f79ec4b38c88bcaa105bc750`。
全検査の前後でバイナリと checker ソースが一致する。

| 検査 | 対象と依存の受理 | ソースから検査 | 再利用 | 終了コード |
| --- | ---: | ---: | ---: | ---: |
| `focused` | 1,543 | 0 | 1,543 | 0 |
| `local` | 1,543 | 230 | 1,313 | 0 |
| `product_integration` | 450 | 118 | 340 | 0 |
| `inverse_implicit` | 793 | 337 | 457 | 0 |
| `euclidean_measure` | 398 | 29 | 311 | 0 |
| `euclidean_forms` | 583 | 154 | 499 | 0 |
| `smooth_bundles` | 1,465 | 748 | 1,090 | 0 |
| `manifold_gluing` | 2,010 | 1,215 | 992 | 0 |
| `compact_support_k` | 2,724 | 1,802 | 1,379 | 0 |

受理列は報告内のモジュールパス数、検査・再利用列は checkpoint の読み込みも含む checker の処理統計である。

`local` は A04 の全230モジュールを `--full-check-local` でソースから検査する。
対象・回帰の全ソースと alias が全体検査の固定 snapshot と一致する。
対象・回帰はすべて worker 1個、回復0、キャッシュ保存失敗0、破損読み取り0。

通常全体検査は全12,944対象を受理した。
新規11,008、再利用1,936、CLI実行103回、すべて終了コード0。
キャッシュ保存失敗0、破損読み取り0、worker回復0回、backend checkpoint再開93回。
全体のworker最大RSSは9,221,776 KiB、最大仮想メモリは11,559,644 KiB。
全体検査の初期・最大上限とキャッシュ予算は12 GiB、対象・直接依存回帰の上限は8 GiB、統合済み B07・G04 の回帰は6 GiB、全体検査と並行した `compact_support_k` は12 GiB、16 GiB cgroupで実行した。
キャッシュを保持し、通常のソース・依存照合を使った。

全11,638ファイルの snapshot、checkout、対象コミットのバイト列を照合した。
全体検査の開始・終了 snapshot と対象一覧も一致し、最新 main の既存成果を含む。

[verification.json](verification.json) に正確な命令・終了コード・ソース・資源とキャッシュ統計を記録する。
`repository.json.gz` は全体集計、`worker-reports.json.gz` は全CLI報告、`targets.json.gz` は対象一覧である。
`source-sha256.json.gz`、`aliases.json.gz`、`checker-source-sha256.json.gz` と対象・回帰・ビルド・全体ドライバの報告・ログも同梱する。

主定理 `Change.theorem` の適用範囲は任意次元の開集合間の滑らかな微分同相と、終域内に台を持つ滑らかなコンパクト台関数である。
一般線形の外測度変換は任意集合を扱い、可測性の保存と Lebesgue 測度の変換を含む。
独立の読み取り専用レビューでも重大な数学的問題や結論を仮定へ隠した箇所は見つからなかった。
