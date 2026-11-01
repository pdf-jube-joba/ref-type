# A06 G03 統合検査記録

検査対象は merge commit `1784dd86111cdf70da2294c2af4d86e39ac91e04`。
G03 を含む main `5e77aab88122f9f3e4f18743fbc474c83b3f8e9a` を取り込んだ。
A06 の package tree は取り込み前 `064b31df7ab333d394ab8566375cc1dd21f451de`、G03 の package tree は incoming main と完全に一致する。
共有登録と README の両パッケージの項目を保持した。

通常全体検査は 11319/11319 対象を受理した。
新規 312、再利用 11007、保存失敗 0、破損読み取り 0、worker 回復 0、終了コード 0。
開始・終了の source snapshot と対象一覧が一致し、保存時に全ソースのバイト列を checkout と照合した。
checker バイナリは開始・終了で一致し、SHA-256 は `a92c84f2ffd0ab3f333a01de0301f647e347a2ec774f30cbba85c062c4346726`。

A06 `--full-check-local` は新規 131・再利用 734、A05 回帰は新規 0・再利用 870、G01 回帰は新規 0・再利用 581。
全て終了コード 0、保存失敗 0。各開始・終了 snapshot と全体検査 snapshot のソース一致も確認した。

通常 release checker の再ビルドは終了コード 0。
対象・依存検査の開始時には cargo が完了処理中だったが、既存 checker と再ビルド後のバイナリのバイト列は同一である。
通常全体検査は再ビルド完了後に実施した。
16 GiB cgroup、全体検査の初期・最大メモリはいずれも 12 GiB、対象・依存検査は 4 GiB。
キャッシュを保持し、通常のソース照合を使った。検証回避フラグは使用していない。

全 A06 要件の実装済み状態を維持している。π は Gaussian 積分から構成し、逆変換の係数は `(2π)^(-n)`。
具体的な命令、時間、資源、キャッシュ統計は [verification.json](verification.json) に記録する。
圧縮した全体・対象・依存の報告、全対象一覧、全ソースの SHA-256 manifest を同梱した。
`../complete` は G03 統合前、`../preservation` と `../foundation` は途中段階の記録である。
