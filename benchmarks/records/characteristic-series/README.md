# L04 特性級数の検証記録

実装 commit: `eb2835f0d5afd6eeed227d7522fb06d4c25ed290`。
基点 main: `bd8fd86d5368968ff22e06f81beb5469bc348623`。
処理系 SHA-256: `6ad1ed33c8ada906086b47d9367becfe019fc4631522ee4d7bc4fb5594e57630`。
対象の `.ref` と manifest の SHA-256: `1b1f09b8b96e3c414f8c227bf123e196bec343bb63178cd97d8359ce7cc16891`。

`libs/refcache/` を共有し、既定の3072 MiB制限、300秒の時間上限で検査した。
対象の `--full-check-local` は全宣言を再検査し、依存先の検証済みキャッシュを再利用した。
続く package 全体検査はソース・manifest・依存入力を照合したキャッシュ再利用による検査である。

| 検査 | 結果 | 経過秒 | 最大 RSS MiB | ソース検査ステップ | 再検査 module | 再利用 module |
| --- | --- | --- | --- | --- | --- | --- |
| 対象 `--full-check-local` | accepted | 21.015 | 622.3 | 14572 | 28 | 166 |
| 依存込み通常検査 | accepted | 0.525 | 291.9 | 0 | 0 | 422 |

worker 数は各1、復旧・重複実行・再実行・失われたステップ・キャッシュ保存失敗はすべて0。

```sh
target/debug/cli libs/algebra/characteristic_series --module characteristic_series --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/l04-target-final.json
target/debug/cli libs/algebra/characteristic_series --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/l04-dependencies-final.json
python3 libs/algebra/characteristic_series/tools/generate.py
git diff --exit-code -- libs/algebra/characteristic_series/src libs/algebra/characteristic_series/tools
```

生成器の再実行による差分がないことと `git diff --check` を確認した。
未解決の証明・検査失敗はない。
