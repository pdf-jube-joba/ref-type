# K11 固定ソースの検査記録

数学ソースは `a7de32d335b2301f073a67f83eeb1d263cb464f8`、統合 main は `4d92b63566b7170526442de2a2979b9f36d85ab0`。
B07・G04・A04 を含む main 上で、Koszul Thom 類、Bott 外積同型、一般 Thom 同型、自然性・直和・合成・実束の複素化を実装した。完了した K11 計画を削除し、以後のコミットは検査証跡と README のみを変更する。

通常 release checker のビルドは終了コード0。rustc・cargo は1.99.1で、バイナリ SHA-256 は `eea3ef7507622c9395d83c0377f9d40c52b78dd02b558ead1db8a58cba092c63`。全検査の前後でバイナリと checker ソースが一致する。

| 通常検査 | 対象と依存の受理 | execution.source_steps | worker / recovery | 終了コード |
| --- | ---: | ---: | ---: | ---: |
| `target` | 3,471 | 13,024 | 2 / 1 | 0 |
| `thom_spaces` | 2,012 | 0 | 1 / 0 | 0 |
| `relative_k_theory` | 1,682 | 0 | 1 / 0 | 0 |
| `periodic_k_theory` | 2,405 | 0 | 1 / 0 | 0 |
| `compact_support_k` | 2,724 | 0 | 1 / 0 | 0 |
| `smooth_bundles` | 1,465 | 0 | 1 / 0 | 0 |
| `manifold_gluing` | 2,010 | 7,980 | 1 / 0 | 0 |
| `change_of_variables` | 1,543 | 9,925 | 1 / 0 | 0 |

受理列は JSON の `verified_modules` のモジュールパス数、source steps は worker 復旧前の処理も含む `execution.source_steps` である。
公開 API 検査はメモリ上限到達後に一度 checkpoint から復旧した。復旧後の最終 worker は検証済み3,471モジュールを通常照合・再利用して受理したため、最終 `checking.checked_steps` は0である。元報告に workers、recoveries、lost_steps、再利用数をそのまま保存している。
宣言・本体・依存を省略しない通常 CLI を使用し、ソースと alias は全体検査の固定 snapshot と一致する。

全リポジトリ検査は全13,794対象を受理した。新規11,423、再利用2,371、CLI実行104回。
キャッシュ保存失敗0、破損読み取り0、worker復旧2回、backend checkpoint 再開43回。
全体の worker 最大 RSS は11,055,328 KiB、最大仮想メモリは12,432,824 KiB、実行時間は2866.5秒。

対象・回帰の仮想メモリ上限は12 GiB。全体検査は初期12 GiB・最大14 GiB、キャッシュ予算12 GiB、16 GiB cgroupで実行した。キャッシュを保持し、通常のソース・依存照合と checkpoint を使用した。

全12,485入力ファイルを checkout と固定数学コミットの Git blob に照合した。全体検査の開始・終了 snapshot 内容と対象一覧も一致する。

[verification.json](verification.json) に正確な命令、終了コード、ソースハッシュ、資源・キャッシュ統計を記録する。
`repository.json.gz` は全体集計、`worker-reports.json.gz` は全CLI報告、`targets.json.gz` は対象一覧である。
`source-sha256.json.gz`、`aliases.json.gz`、`checker-source-sha256.json.gz` と対象・回帰・ビルド・全体ドライバの元報告・ログも保存する。

親からの独立レビューでは、この時点で数学的な重大問題は報告されていない。局所類比較・直和同型・複素化の最終アダプターも別途読み取り専用で確認した。最終レビューとマージは親が担当する。

開発途中の記録は [checkpoint 履歴](../k11-k-thom-checkpoint/README.md) に残している。履歴中の未完・未検査という記述は各保存時点の状態である。
