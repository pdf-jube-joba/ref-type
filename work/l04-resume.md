# L04 の再開と検証

基点: main bd8fd86d5368968ff22e06f81beb5469bc348623。
作業先: /workspace/ref-type-l04、ブランチ codex/l04-characteristic-series。

実装済み: 有理係数対称多項式、任意次数の Newton 恒等式、切断級数の演算、非零定数項の逆、指数、生成級数・乗法列の切断整合性、次数4/8の普遍公式、利用例と公開 README。
検査器と依存ライブラリのソースは基点のままである。
生成証明は `python3 libs/algebra/characteristic_series/tools/generate.py` で再生成できる。

```sh
cd /workspace/ref-type-l04
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --module characteristic_series --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/l04-target-final.json > work/l04-target-final.log 2>&1
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/l04-dependencies-final.json > work/l04-dependencies-final.log 2>&1
```

workspace 共通の `libs/refcache/` を再利用する。
処理系がない場合は `CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline` でビルドする。
対象28 module・14,572ステップの再検査と、依存込み422 module のキャッシュ検査が成功済み。
最終レポートは `benchmarks/records/characteristic-series/` に保存した。
生成器の再実行による差分がないことと `git diff --check` も確認済み。

初期の具体的な有理数証明では180秒の時間上限と stack overflow が発生した。
分数の拡大・約分と同分母加算の一般補題を用いる証明へ置き換え、その後の全対象検査は約21秒で完了した。
検査規則は変更していない。

証明と検査に未解決事項はない。
PR に検証結果を記載し、作成後は停止する。
