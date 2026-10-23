# 大規模検査の宣言共有と継続実行

名前空間の宣言を参照時に具体化する view に変え、検査セッション、ページ化した式ストア、checkpoint による復旧を接続した。

## 条件と再現

2026-10-22、Intel Core i5-12400、WSL2、メモリ約15.5 GiBで計測した。
旧方式は `54d2e585dfaa5ccfa0844c9e1026e6da82007ab9` のソースを展開し、新方式と同じRust 1.99.1、dev profileでビルドした。
詳細は [environment.json](environment.json) に記録した。
ビルドとテストを終えてから計測を順番に実行し、通常計測と詳細プロファイルも分けた。
個別選択と再利用は3回、長い全体検査と詳細プロファイルは各1回である。

```sh
python3 benchmarks/large_scale_suite.py \
  --binary target/debug/cli \
  --baseline benchmarks/runs/large-scale-checking/baseline-target/debug/cli \
  --output benchmarks/runs/large-scale-checking/final-verified
```

計測中に保存頻度の問題が見つかったため、`finite_models` の全体検査・再利用と退避・再読込の軸は修正後のバイナリ（SHA-256先頭 `b1145476`）で再計測した。
個別選択・詳細プロファイル・他の2ライブラリ・残りの規模軸は修正前（`9bd1f463`）の記録である。
変更はメモリ回収要求に伴うcheckpointの最小間隔で、後者の条件はcache無効または回収要求0回だった。
保存失敗の診断表示はその後に修正し（`b4840b33`）、再開・編集・保存失敗の試験と既存テストを最終バイナリで実行した。
検査ロジックと保存形式はこの診断表示の変更では変わらない。

実行したコマンド、バイナリと入力のSHA-256、各回のCPU時間・最大RSS・終了状態は個別のJSONに含む。
最大RSSは `wait4` による子孫を含む個々のプロセスの最大値で、同時点の全プロセスの合計ではない。
新方式の `execution.peak_virtual_kib` はsupervisorが観測したworkerの仮想メモリである。
旧方式のレポートにはこの観測項目がない。
式ページの常駐量・索引容量・退避量は内部の容量概算で、OSのRSSとは区別する。
ページの読込量は符号化データ量、退避量は繰り返し退避したページのメモリ量の累積であり、物理ディスクへの転送量やRSSの純減とは異なる。

## finite_models の全体検査

[full-finite-models-8192.json](full-finite-models-8192.json) は `--full-check`、8192 MiB、3600秒上限、1回の計測である。
863.304秒で受理され、依存先を含む4,105ファイルをparseし、全5,117モジュール・68,669検査ステップを完了した。
workerは1個、復旧・ソース検査の重複・再実行・未保存の作業はすべて0で、最終checkpointも68,669ステップを含む。
入力とバイナリは実行中に変化していない。
user timeは651.934秒、system timeは40.404秒、最大RSSは6,018,252 KiB、workerの最大仮想メモリは7,497,800 KiBだった。
時間には最終保存とsupervisorによる成果物の公開を含めた。

[中間実装](intermediate-full-8192.json) でも同じ入力・coverageを903.250秒で受理したが、最大RSSは6,994,360 KiB、最大仮想メモリは8,026,288 KiBだった。
その後、resolverの大域表の共有、検査済みHIRの解放、intern候補キーの縮小を加えた。
最終実装ではRSSが約0.93 GiB減り、式索引の容量も1,113,349,224 byteから880,316,888 byteへ減った。
この比較は実装途中の保持方式の改善であり、旧方式に対する全体検査の速度比ではない。

[保存間隔の修正前](full-finite-models-8192-before-spacing.json) は902.424秒、環境書込2,487,296,578 byteだった。
メモリ圧迫中も前回の保存コストに応じた間隔を設けた後は863.304秒、1,799,442,828 byteとなった。
回収は直ちに行い、保存処理中に届いた次の回収要求が保存の連続実行につながることを防いでいる。

[旧方式の全体検査](baseline-full.json) は8192 MiBで600.188秒の打切りとなり、最大RSSは6,751,464 KiBだった。
全件の受理は確認できておらず、この打切り値と新方式の完走時間から速度比は算出しない。

## メモリ上限と異なる依存構造

いずれも依存先を含む `--full-check`、3600秒上限、各1回である。

| 入力 | 上限 MiB | 経過秒 | 最大RSS KiB | 最大仮想メモリ KiB | worker / 復旧 | 完了ステップ | 結果 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: | --- |
| finite_models | 8192 | 863.304 | 6,018,252 | 7,497,800 | 1 / 0 | 68,669 | 受理 |
| finite_models | 3072 | 254.609 | 2,814,132 | 3,118,964 | 2 / 1 | 40,121 | メモリ上限 |
| singular_cohomology | 8192 | 134.788 | 1,792,100 | 2,385,372 | 1 / 0 | 29,156 | 受理 |
| singular_cohomology | 3072 | 133.370 | 1,791,444 | 2,385,372 | 1 / 0 | 29,156 | 受理 |
| manifolds | 8192 | 56.929 | 939,540 | 1,337,044 | 1 / 0 | 18,193 | 受理 |
| manifolds | 3072 | 54.268 | 939,716 | 1,337,040 | 1 / 0 | 18,193 | 受理 |

[finite_models 3072](full-finite-models-3072.json)、[singular_cohomology 8192](full-singular-cohomology-8192.json)・[3072](full-singular-cohomology-3072.json)、[manifolds 8192](full-manifolds-8192.json)・[3072](full-manifolds-3072.json) にCPU時間と保存・読込量も含む。
`singular_cohomology` は1,826ファイル・2,362モジュール、`manifolds` は1,280ファイル・1,468モジュールを検査した。
成功した5条件はすべてソース検査の重複・再実行・未保存の作業が0だった。

**finite_models の3072 MiB目標は未達である。**
38,832ステップのcheckpointから1回復旧したが、その後も上限に達した。
公開済み範囲の再検査はなく、未保存の1ステップが再実行された。
`lost_steps=1290` は2回の停止で失った実行回数の合計で、最終checkpoint以降に完了していた異なるステップは1,289個である。
終了状態は型エラーと区別した `memory-limit` であり、この条件を完走や受理として扱わない。

最終的な全件環境では、式の索引が約840 MiB、名前空間の固定部分が約485 MiB、binding表が約154 MiB、resolverのscope配列が約160 MiBである。
これに引数環境、名前・置換表、展開テンプレート、入力構文木、作業領域とallocatorの保持分が加わる。
式本文は回収後約64 MiB、最終境界のpinは15ノードであり、本文の退避だけで3072 MiBへ収めることはできていない。
I/Oバッファはページの64 KiB、索引segmentの16〜128 KiB、復元の1 MiBに分けたが、共有表の符号化・復元用の索引は別に必要になる。

[resolver単体の補助計測](resolver-retention.json) では、入力構文木だけで311,340 KiB、全packageの名前解決と検査入力の解放を模擬した後で1,373,892 KiB、元の入力構文木を解放すると1,110,496 KiBのRSSだった。
6,536個のソースmodule、554,452個のinstance scope、439,759個の引数環境、134,125個の共有引数式を保持する。
この計測はsystem allocatorを使い、各観測前に `malloc_trim` を呼んだもので、elaboration・kernelの状態や実際の型検査を含まない。
CLIとはallocatorも異なるため、これをCLIのRSSへそのまま加算することはできない。

全件検査の圧縮済み環境の書込は約1.80 GB、読込は約11.44 GB、終了後の実キャッシュ量は約1.25 GiBだった。
式ストアのページ読込は約34.46 GB、1,557,659回で、退避量は約444 GBだった。
保持量を抑える一方で再読込が多く、入力索引の保持と並んで残る費用である。

## 保存済み結果の再利用

全件検査後の同じcacheを使い、8192 MiBで各3回実行した。
通常検査は全9回でソース検査ステップ0、`--full-check-local` は依存環境を復元して入口packageを再検査した。
全18回で受理され、worker 1個、重複検査・復旧・再実行は0だった。

| 入力 | 通常検査の中央値 秒 | 局所再検査の中央値 秒 | 局所再検査のステップ | 局所再検査の最大RSS KiB |
| --- | ---: | ---: | ---: | ---: |
| finite_models | 0.850 | 200.490 | 4,740 | 6,837,604 |
| singular_cohomology | 0.386 | 30.490 | 3,373 | 2,034,376 |
| manifolds | 0.244 | 10.902 | 2,721 | 1,048,948 |

[finite_models 通常](warm-finite-models.json)・[局所再検査](full-local-finite-models.json)、[singular_cohomology 通常](warm-singular-cohomology.json)・[局所再検査](full-local-singular-cohomology.json)、[manifolds 通常](warm-manifolds.json)・[局所再検査](full-local-manifolds.json) に各回のCPU時間・保持量・保存量を記録した。
`finite_models` の局所再検査は4,852モジュールを再利用し、対象265モジュール・4,740ステップを検査した。
時間は212.386 / 198.324 / 200.490秒だった。
[保存間隔の修正前](full-local-finite-models-before-spacing.json) は207.189 / 253.563 / 352.963秒、環境書込は約0.72 / 1.12 / 1.93 GBで、繰り返しごとに増えていた。
修正後の環境書込は約0.72 / 0.45 / 0.44 GBとなり、各回の途中checkpointは1回だった。

## 個別選択

`libs/topology/examples/finite_models` を入力に `--module-only --no-cache`、8192 MiB、600秒上限で計測した。
全件受理で、検査結果の再利用はない。

| 選択 | 旧方式の中央値 秒 | 新方式の中央値 秒 | 旧方式の最大RSS MiB | 新方式の最大RSS MiB |
| --- | ---: | ---: | ---: | ---: |
| Graph.On.With | 3.035 | 4.772 | 699.3 | 676.6 |
| MayerVietoris.Over.On.Chains | 6.260 | 8.616 | 1024.4 | 815.0 |
| Torus.Geometry.Ring.Primitive | 71.654 | 95.327 | 5875.5 | 2047.6 |

[Graph旧](selected-baseline-graph.json)・[Graph新](selected-current-graph.json)、[Chains旧](selected-baseline-chains.json)・[Chains新](selected-current-chains.json)、[Torus旧](selected-baseline-torus.json)・[Torus新](selected-current-torus.json) に各回の値を保存した。
TorusではRSSが約65%減った一方、時間は約33%増えた。
小さい選択範囲も速くなったとはいえず、本文を常駐させないことと再読込の費用の交換になっている。

Torusの新方式では3,728,759個の定義IDを予約し、実際に確保した宣言セルは35,502個、具体化した定義は15,689個、inductiveは6,399個だった。
式ストアには13,819,976スロット、8,917,097生存ノードがあり、索引容量は約212 MiB、常駐ページは約128 MiBだった。
読込は約3.16 GB、退避は約43.5 GB、ページ読込回数は152,949回である。

詳細計測は [Torus旧](profiles-baseline-torus.json)・[Torus新](profiles-current-torus.json) に保存した。

| 排他的な処理群 | 旧方式 秒 | 新方式 秒 |
| --- | ---: | ---: |
| namespace | 35.326 | 30.432 |
| kernel | 21.631 | 31.403 |
| query | 8.511 | 23.151 |
| bridge | 5.790 | 8.542 |
| resolve | 3.305 | 2.581 |

旧方式の `namespace.definition-fresh` は3,722,640件で、新方式ではその宣言ごとの予約経路を廃止した。
新方式の `namespace.views` は再利用を含むview処理件数の累積1,490,901件で、最終的に保持したviewは302,609個である。
詳細計測の経過時間は旧77.599秒、新100.533秒なので、上表を通常計測の秒数に配賦しない。

## 規模による増加

各サイズ3回、式ページの常駐予算1 MiBで測定した。
時間は中央値、保存量は1回目の実キャッシュ量である。

| 変化させた軸 | サイズ | 経過秒 | 検査ステップ | 具体化した定義 | 保存byte |
| --- | ---: | ---: | ---: | ---: | ---: |
| 依存チェーン | 16 / 32 / 64 | 0.907 / 1.914 / 3.023 | 559 / 1119 / 2239 | 0 / 0 / 0 | 158417 / 321533 / 643157 |
| 共通依存の利用側 | 16 / 32 / 64 | 0.686 / 1.290 / 2.460 | 98 / 162 / 290 | 16 / 32 / 64 | 38975 / 76830 / 155656 |
| namespaceの幅 | 16 / 32 / 64 | 0.102 / 0.102 / 0.102 | 84 / 100 / 132 | 2 / 2 / 2 | 13971 / 15498 / 18514 |
| import数 | 16 / 32 / 64 | 0.102 / 0.102 / 0.102 | 68 / 100 / 164 | 2 / 2 / 2 | 11335 / 15892 / 24304 |
| 局所文脈のimport数 | 16 / 32 / 64 | 0.102 / 0.102 / 0.102 | 52 / 68 / 100 | 0 / 0 / 0 | 9006 / 11151 / 15457 |

[chain](scaling-chain.json)、[consumers](scaling-consumers.json)、[width](scaling-width.json)、[imports](scaling-imports.json)、[locals](scaling-locals.json) に各回のRSS、仮想メモリ、宣言セル・索引・ページの保持量も含む。
すべてworker 1個、ソース検査の重複0で受理された。
チェーンはpackageの追加ごとに35ステップ増え、完了済みprefixの再検査は生じていない。
共通依存の利用側では、基礎の34ステップを一度検査し、利用側ごとに4ステップ増えている。
namespaceの幅とimport数を増やした場合も、使用した2種類の引数に対する具体化は2個のままだった。
約0.1秒の短い実行では起動・監視時間の影響が大きく、時間の横ばいだけから増加率を判断しない。

[退避・再読込](scaling-resident.json) は各群128個の独立した型と定義を作り、全群の後に古い型別名の本文をconversionで参照する。
式ページの予算は1 MiB、各サイズ3回である。

| 群の数 | 経過秒の中央値 | 検査ステップ | ページ読込回数 | ページ退避回数 | 読込byte | 保存byte |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 64 | 3.554 | 32,962 | 78 | 94 | 1,437,446 | 5,098,288 |
| 128 | 6.827 | 65,922 | 159 | 195 | 2,961,123 | 10,376,105 |
| 256 | 14.271 | 131,842 | 322 | 398 | 6,101,224 | 21,388,899 |

全9回で受理され、ソース検査の重複・復旧は0だった。
完了した本文を退避し、後続の検査で再読込しても原形の検査をやり直していない。
最終常駐ページは894,624 byteで、追加・読込ページを含む一時的な最大値は1,287,424 byteだった。
RSSは最大約845 MiBまで増えており、ページ予算は入力・索引を含むプロセス全体の上限ではない。
単純な独立宣言で管理処理の増え方を測っており、実ライブラリの型検査やconversionの難しさは別に評価する。

## 再開と編集

[cache-recovery.json](cache-recovery.json) は16段の依存チェーン、diamond、依存順変更、別の利用側、入口編集、依存編集を各1回確認した記録である。
中断試験はcheckpoint公開後に終了を通知し、再開とその後の無変更検査が受理されることを確認した。
自動復旧試験ではsupervisorを残してworkerだけをSIGKILLし、2個目のworkerが同じ要求を完了した。
548ステップのうち再実行したのはcheckpoint公開後の未保存の1ステップで、公開済みステップの再検査は0だった。
自動復旧を含む所要時間は5.710秒である。

保存失敗は `checkpoints/` の位置に通常ファイルを置いて再現した。
検査自体は20ステップすべてを受理し、26回の保存失敗と最後のI/Oエラーがレポートに残った。
`--no-progress` でも標準エラーへ保存失敗の診断が表示された。
障害を除去した後の強制検査は保存失敗0回で成功し、最終checkpointが20ステップを含むことを確認した。

## 既存の検証

[verification.json](verification.json) に実行コマンドとバイナリのSHA-256を記録した。
`cargo test --workspace --locked` は379件成功、`cargo fmt --all -- --check` と `cargo clippy --workspace --all-targets --locked -- -D warnings` も成功した。
`cargo build --workspace --locked` 後の `python3 tests/tests.py` は401件成功、失敗0件だった。
module引数、局所文脈、nominal identity、Program、部分成果物の統合順、checkpointの再開と失効を既存ケースで確認した。

ベンチマーク用Pythonテスト6件と、補助resolverのビルド・clippyも成功した。
