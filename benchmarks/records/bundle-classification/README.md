# B06 束の分類写像と安定化の通常検査

基準 main は `5d213f86a635f17f309f058d929002e2840f393b`、実装ブランチは `feat/b06-bundle-classification`。
実装は `libs/geometry/bundle_classification` の111 source module と package 登録、利用例、文書に限定する。
既存数学ライブラリと Rust 処理系のソース変更はない。

2026-10-30 のクラウド環境で、コンテナのメモリ上限16 GiBを確認した。
通常検査は単一 worker、初期・最大仮想メモリ10240 MiB、キャッシュ予算12288 MiB、空き容量目安256 MiBで行う。
通常の検証済みキャッシュと checkpoint を照合して再利用する。

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked
python3 scripts/check_all.py libs/geometry/bundle_classification --state-dir work/b06-package --initial-memory-mib 10240 --memory-mib 10240 --cache-budget-mib 12288 --min-free-mib 256
python3 scripts/check_all.py --state-dir work/b06-whole --initial-memory-mib 10240 --memory-mib 10240 --cache-budget-mib 12288 --min-free-mib 256
```

対象を列挙して固定した source snapshot に対して検査し、終了時に source・対象一覧・処理系の一致を確認する。
実行ログ、全対象、source snapshot、各 package のレポート、最終集計は各 state directory に保持する。
