# L04 検査の再開

基点: main bd8fd86d5368968ff22e06f81beb5469bc348623。
作業先: /workspace/ref-type-l04、ブランチ codex/l04-characteristic-series。

```sh
cd /workspace/ref-type-l04
CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline
mkdir -p work
/workspace/ref-type/target/debug/cli libs/algebra/characteristic_series --cache-stats --diagnostics compact --report-json work/l04-check.json
```

workspace の libs/refcache を再利用する。
検査結果と残作業は、このファイルを各 checkpoint で更新する。
現在は有理数の環構造を既存の商 API から構成した段階で、検査は未実施。
次に有限切断級数、対称多項式と Newton 恒等式、特性級数係数と利用例を構成する。
