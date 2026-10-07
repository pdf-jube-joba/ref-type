# キャッシュなしのライブラリ検査（2026-10-05）

## 測定条件

2026-10-05、Linux x86_64、Rust 1.95.0、既存の dev profile（`opt-level = 2`、debug assertion と debug 情報あり）で測定した。
基準は category の高速化を統合済みの main `62285441fd9f895732494b9b81110f316bd25997` の処理系であり、比較する両方の版に整理後の同じ `libs/` を与える。
各ライブラリを新しい CLI プロセスで3回検査し、`--no-cache --diagnostics compact` を指定する。
検査中にビルドや別の計測を並行実行しない。
経過時間にはプロセスの起動から終了までを含め、Linux の `wait4` でプロセスごとの user/system CPU 時間と最大 RSS を採る。
ディスクの検証済み結果は読み書きせず、依存ライブラリも各プロセスで検査する。
OS のファイルキャッシュは消していない。

```sh
cargo build -p cli
python3 tests/bench_libraries.py --binary target/debug/cli --runs 3 --output /tmp/library-after.json
python3 tests/bench_libraries.py --binary /path/to/before-cli --runs 3 --output /tmp/library-before.json
REF_TYPE_PROFILE_PHASES=1 REF_TYPE_PROFILE_DECLARATIONS=1 REF_TYPE_PROFILE_MODULES=1 \
  target/debug/cli libs/category --no-cache --diagnostics compact --stats
```

計測スクリプトは CLI とライブラリソースの SHA-256、実行設定、個々の測定値、検査ログを保存する。
プロファイル用の環境変数は通常のベンチマークから除き、プロファイル実行は時間比較とは別に行う。

## 対象の改善

lowering の共有キーを束縛の深さで管理し、型への同時代入を共有した。
kernel に登録済みの宣言の依存先の再走査を省き、module 引数の閉性に既存の自由変数情報を使った。
共有表は環境内で保持し、一時ノードの回収時に整理する。

## 当時の結果

各値は3回の中央値（最小〜最大）、RSS は3回で観測した最大値である。
合計は各巡の経過時間の和の中央値であり、各行の中央値の和とは一致しない場合がある。

| ライブラリ | main 秒 | 統合版 秒 | 短縮率 | 最大RSS 前→後 MiB |
| --- | ---: | ---: | ---: | ---: |
| `std` | 2.608（2.543〜2.646） | 2.469（2.430〜2.557） | 5.3% | 571.4 → 577.6 |
| `real` | 6.952（6.812〜7.318） | 6.580（6.511〜6.651） | 5.4% | 881.8 → 902.9 |
| `complex` | 8.107（7.873〜8.280） | 7.550（7.264〜7.574） | 6.9% | 948.2 → 957.1 |
| `linear_algebra` | 10.414（10.397〜10.477） | 9.541（9.277〜9.603） | 8.4% | 1075.4 → 1095.5 |
| `topology` | 11.247（11.098〜11.309） | 10.071（10.000〜10.389） | 10.5% | 1194.5 → 1211.9 |
| `calculus` | 7.456（7.371〜7.502） | 7.120（7.036〜7.134） | 4.5% | 930.7 → 951.8 |
| `integration` | 9.584（9.535〜9.755） | 8.697（8.695〜8.852） | 9.3% | 985.5 → 1002.4 |
| `category` | 9.753（9.738〜9.915） | 8.302（8.225〜8.912） | 14.9% | 716.0 → 754.3 |

合計は **66.099秒 → 60.618秒、8.3%短縮**した。
各巡の合計は main 66.649, 66.099, 65.945 秒、統合版 59.828, 60.618, 60.994 秒だった。
category は **9.753秒 → 8.302秒、14.9%短縮**し、既存の高速化を保った。
全24回の最終ライブラリ検査が成功した。
追加の共有表によってメモリは増え、全ライブラリ中の最大値は1194.5 MiBから1211.9 MiBとなった。
category 単体の最大値は716.0 MiBから754.3 MiBとなった。

当時の検証は workspace の307テストと全8ライブラリで成功した。
この表の生データ `doc/benchmarks/library-checks-2026-10-05.json` は、この checkout には含まれていない。
現行版の測定には上記のスクリプトを使う。


## G05 の計測（2026-10-07）

同じ dev profile で、G05 の式中の module 具体化と再利用処理を測定した。
[測定値](benchmarks/g05-2026-10-07.json) に hyperfine の各実行時間と GNU time の最大 RSS を保存した。

500個の定義が同じ恒等関数を参照する小さな入力を5回ずつ検査したところ、通常の関数参照は G05 対応前21.5 ± 1.5ms、対応後21.8 ± 1.2ms、一時 module を介する参照は28.0 ± 1.1msだった。
各値は平均と標準偏差であり、この入力では既存構文の明確な速度低下は見られなかった。

```sh
perf record -F 49 --call-graph dwarf,8192 -o /tmp/g05.perf -- \
  target/debug/cli tests/projects/module-expressions --no-cache --diagnostics compact
perf report -i /tmp/g05.perf --stdio --no-children --percent-limit 2 --sort symbol
```

実ライブラリの検査では `reuse_lazy_definition` が CPU cycle の自己サンプルの約9%を占め、`Arena::get`、ノード比較、確保も上位に現れた。
元の宣言ごとに再利用候補を索引化する変更を試したが、`std` の5回測定は2.533 ± 0.042秒→2.497 ± 0.037秒、大きな G05 の実例の各1回測定は73.797秒→87.077秒となった。
後者の最大 RSS は3268076 KiB→3268200 KiBで、両方の検査が成功した。
単発測定には変動があるものの速度改善を確認できず、索引化は採用していない。

G05 の8テストを valgrind の Memcheck でも検査し、エラー0件、definitely lost と indirectly lost は0 bytesだった。
Rust のテストランナーのスレッド初期化に由来する possibly lost 48 bytes と still reachable 548 bytes が残った。
このメモリ検査は小さな回帰テストを対象とし、実ライブラリ全体を対象とするものではない。
