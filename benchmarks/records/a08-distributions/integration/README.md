# A08・G05 統合検査

検査した head は `cc433cf0b1d3fa1dfb35c7aef2cbba947edbd19f`、取り込んだ main は `60d033e2b84aa77a220a18a29a1df3cd7bd2592e`。
A08 と G05 の数学ソースをそれぞれ統合前 A08 と main の Git tree と照合し、一致を確認した。
登録・API 索引は両 package を含み、main の取り込みに競合はなかった。
`src/USAGE.md` と `src/sema/README.md` の保存間隔の説明を、処理系の指定周期上限へ合わせた。

処理系184ファイルのハッシュとバイナリ SHA-256 `915f17d4d0720b8165e1dd521df1a033265365e5bfa085a069e8fad93cdbda22` は、[統合前の検査](../README.md) と一致する。
その release build と checkpoint 回帰13件の受理結果を再利用し、処理系を再ビルドしなかった。

| 対象 | 受理した依存閉包 | ソースから検査した module | 終了コード |
| --- | ---: | ---: | ---: |
| `a08` | 1,611 | 0 | 0 |
| `g05` | 1,981 | 280 | 0 |

統合全体検査は全 14,111 対象を受理し、終了コード0。
新規 0、再利用 14,111、CLI 実行 106 回。
保存失敗 0、破損読み取り 0、worker 回復 0、checkpoint 再開 0。
最大RSS 1,626,308 KiB、最大仮想メモリ 2,117,972 KiB。
通常の検証済みキャッシュを利用し、全 12,804 ソースを開始時snapshot・最終checkout・検査コミットのGit blobと照合した。
全体ドライバも終了時にソース・対象一覧・バイナリの同一性を検査した。

```sh
REF_TYPE_GRAPH_SPILL_DIR=/tmp python3 scripts/check_all.py --initial-memory-mib 15360 --memory-mib 15360 --cache-budget-mib 16384 --state-dir work/a08-integration-check
```

[verification.json](verification.json) は正確な package コマンド、結果、同一性確認、全体集計を持つ。
圧縮した全体・worker・package報告、対象一覧、ソースハッシュ、alias一覧、driver出力も保持する。
この記録を追加するコミットは数学ソースと処理系ソースを変更しない。
