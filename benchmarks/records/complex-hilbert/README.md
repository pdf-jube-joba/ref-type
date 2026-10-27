# A19 複素 Hilbert 空間の検査記録

検査対象の実装 commit: `cdf279257b140afb3e1a158356e513da5e12af9e`。
基点 main: `bd8fd86d5368968ff22e06f81beb5469bc348623`。
処理系 SHA-256: `6ad1ed33c8ada906086b47d9367becfe019fc4631522ee4d7bc4fb5594e57630`。
対象の `.ref` と manifest の SHA-256: `19b184f7fbd965de0220c2544bf2e176d6c51590957ee4801cb669f41cf12935`。
入力のハッシュはパスの辞書順で `path + NUL + contents + NUL` を連結して計算した。

専用 worktree の `libs/refcache/` を両検査で共有し、既定の3072 MiB制限、300秒の時間上限、worker 1で実行した。
検査前に実装と再開手順を commit・push した。
対象の `--full-check-local` は対象22モジュールの全宣言を再検査し、依存先の検証済みキャッシュを再利用した。
依存込み通常検査は登録された依存パッケージも検査対象とし、入力が一致する検証済みキャッシュを再利用した。
キャッシュを無効化する `--full-check` は使用していない。

| 検査 | 結果 | 経過秒 | 最大 RSS MiB | ソース検査ステップ | 再検査 module | 再利用 module |
| --- | --- | --- | --- | --- | --- | --- |
| 対象 `--full-check-local` | accepted | 3.014 | 626.4 | 315 | 22 | 250 |
| 依存込み通常検査 | accepted | 46.813 | 895.1 | 12241 | 1057 | 172 |

復旧・重複実行・再実行・失われたステップ・キャッシュ保存失敗は両検査とも0。
生の結果は [target.json](target.json) と [dependencies.json](dependencies.json) に保存した。

```sh
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --module complex_hilbert --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-target-final.json
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-dependencies-final.json
```

## 成功・失敗・未実行

- 成功: 実スカラー制限、複素 Hilbert 構造、複素 Riesz 表現、有界随伴、閉部分空間への直交射影、商と直交補の等長線形同型・最小ノルム代表、有限階数の和・前後の合成、`Examples` の小さい利用例。
- 失敗: 最終検査にはなし。開発中の構文・参照・型エラーは修正し、上記の最終検査で再検査した。
- 未実行: コンパクト作用素の構成、有限階数近似との比較、和・合成・ノルム極限・随伴による閉性、コンパクトな恒等作用素からの有限次元性。これらは未実装である。
- 処理系の変更はなく、Rust のテストは実行していない。

未完了の理由と必要な共通 API は [公開 README](../../../libs/analysis/complex_hilbert/README.md#コンパクト性に必要な共通-api) に記載した。
未完了部分は全有界性と有限次元ノルム空間のコンパクト性に関する共有基盤の追加を必要とし、その追加は保留している。
A19 全体の完了を示す検査記録ではない。
