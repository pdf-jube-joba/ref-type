# L04 検査の再開

基点: main bd8fd86d5368968ff22e06f81beb5469bc348623。
作業先: /workspace/ref-type-l04、ブランチ codex/l04-characteristic-series。

```sh
cd /workspace/ref-type-l04
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --module characteristic_series --cache-stats --diagnostics compact --report-json work/l04-target.json
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --cache-stats --diagnostics compact --report-json work/l04-dependencies.json
```

workspace の libs/refcache を再利用する。
処理系がない場合は `CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline` でビルドする。

有理数可換環、任意精度の和・積・単位逆・零定数項での合成・指数、それらの切断整合性を実装済み。
単位逆の積の法則、基本対称式の置換不変性、任意の根数・任意次数での Newton 恒等式を検査済み。
直近の対象検査は work/newton-check.log で成功。
残作業は特性級数・乗法列・次数4/8の係数計算、公開多項式 API、利用例、README、依存を含む最終検査、PR。
