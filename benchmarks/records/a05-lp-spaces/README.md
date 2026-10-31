# A05 Lp 空間の実装と通常検査

最終数学ソースは `d30a2735b0f17f23a18c5c92a630bd6afa49bcfc` で、統合した main は `0ad4e2429fd244a0dd58e6ff725537ce69972be2` である。
この記録を追加するコミットは文書と検査証跡だけを変更する。

| 計画項目 | 公開 API | 達成状況 |
| --- | --- | --- |
| 既存 Lp 商の線形・ノルム構造、Hölder・Minkowski・完備性 | `On.Finite`、`On.Norm`、`On.Holder`、`On.Completion`、`On.Infinity`、`On.Endpoint` | 完了 |
| 実・複素 L2 Hilbert 構造 | `On.Hilbert`、`On.Complex.Complete`、`On.Complex.Characterization` | 完了 |
| 可積分単関数の稠密性 | `On.SimpleApproximation` | 完了 |
| コンパクト台連続・滑らかな関数の稠密性 | `Euclidean.Approximation` | 完了 |
| 平行移動の連続性 | `Euclidean.Translation` | 完了 |
| 近似単位と畳み込み平滑化 | `Euclidean.Convolution.approximateIdentity`、`Smoothing`、`Operator`、`Derivative`、`CompactSupport` | 完了 |
| 代表元・可測性の橋渡し | `Euclidean.BorelRepresentative`、`Euclidean.Joint`、`Convolution.Respects` | 完了 |

Banach・Hilbert 構造と可積分単関数近似は任意の測度上で証明した。
Euclid 上の稠密性・平行移動・近似単位は Lebesgue 測度と有限実指数 \(1\le p<\infty\) に限定し、零次元も含む。
一般の L∞ で滑らかな関数の稠密性は主張しない。
畳み込みは実際の積分であり、全点での積分存在、標準形への変数変換、核の共同可測性、偏微分の積分表示を証明する。

Linux x86_64、Rust 1.95.0、16 GiB の cgroup 上限の環境で実行した。
最終 release ビルド後に対象・関連回帰・通常の全体検査を実行した。
既存キャッシュは通常のソース・依存・処理系照合を通して再利用し、全削除していない。

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked

target/release/cli libs/analysis/lp_spaces --module lp_spaces --cache-dir libs/analysis/lp_spaces/refcache --memory-mib 4096 --no-progress --diagnostics compact --report-json work/a05-final-source-target.json

target/release/cli libs/analysis/functional --module functional_analysis.Measure --cache-dir libs/analysis/lp_spaces/refcache --memory-mib 4096 --no-progress --diagnostics compact --report-json work/a05-final-related-measure.json

target/release/cli libs/analysis/product_integration --module product_integration --cache-dir libs/analysis/product_integration/refcache --memory-mib 4096 --no-progress --diagnostics compact --report-json work/a05-final-related-product.json

target/release/cli libs/geometry/smooth_partitions --module smooth_partitions --cache-dir libs/geometry/smooth_partitions/refcache --memory-mib 4096 --no-progress --diagnostics compact --report-json work/a05-final-related-smooth.json

python3 scripts/check_all.py --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 512 --state-dir work/a05-repository-check
```

対象・関連回帰の終了コードは全て 0 で、対象は依存を含む 870 モジュール、このうち 148 モジュールが `lp_spaces` に属する。
Measure は 244、A03 は 450、G01 は 581 モジュールを確認した。
これらの CLI の新規・再利用カウンタは `verification.json` の `checked_modules_raw`・`reused_modules_raw` に保存する。
CLI の生カウンタは一般には対象集合の排他的な分割を表さない。

全体検査の最終結果とソース一致の確認は `verification.json` の `repository_check` に記録する。
全体検査の新規・再利用数は、ドライバが全対象集合を排他的に分けた件数である。
以前の `8ac8d515` に対する 10,453 対象の全体検査は `baseline_repository_check` に保存し、最終ソースの証跡とは区別する。

| 検査 | 対象数 | 新規 | 再利用 | 終了コード | 保存失敗 |
| --- | ---: | ---: | ---: | ---: | ---: |
| 対象 | 870 | 0 | 870 | 0 | 0 |
| Measure | 244 | 0 | 244 | 0 | 0 |
| A03 | 450 | 450 | 0 | 0 | 0 |
| G01 | 581 | 581 | 0 | 0 | 0 |
| 通常全体検査 | 10641 | 653 | 9988 | 0 | 0 |

全体検査は 95 回の scope 検査で完了し、経過時間は 288.1 秒、最大 RSS は 1,278,152 KiB だった。
キャッシュ書き込み失敗・破損読み込み・worker 復旧は全て 0 で、cgroup の OOM・OOM kill も 0 だった。
開始・終了の source snapshot が一致し、9450 ソースファイルの内容を固定コミットの `git archive` と照合した。
最終再列挙の対象一覧、全検査対象集合、新規・再利用の排他的な和集合、処理系バイナリの SHA-256 も一致した。

- source snapshot SHA-256: `4081005b3f15b839b22e0b555c0713d796f30f5d0fb88b3fd923b6b5c8380d6f`
- release binary SHA-256: `6bad0fbcb9e5ab8be1feea9cd8b8db573c7698cf39381a3d3de0b0a9a4e6b81a`
- 詳細ログ・snapshot・scope 別 JSON: `work/a05-repository-check/20261031T094817.821528Z/`

数学ソースに未実装の計画項目はない。
