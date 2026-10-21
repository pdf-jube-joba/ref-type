# cohomology_examples の全検査コスト

`cohomology_examples` の `--full-check` を計測し、分割後の依存環境の再構築を確認した。
大きな改善候補は、同じ実行内の依存環境の共有と、名前空間の具体化・引数処理の削減である。
全体の完走時間は今回の時間制限内では得られておらず、利用者の「約4時間」という見込みは検証できていない。

## 入力と条件

2026-10-21 の `main`、`ba820d41c13a5ec2b802d72c995eba1d03558130` を使った。
入力は `libs/topology/examples/finite_models` で、module の選択は指定していない。
対象自身は242個の `.ref`、8,962行で、宣言された依存先を含む入力は41 package、4,105個の `.ref`、157,432行である。
CLI の計画には inline module などを含む5,117モジュールがある。
[入力の内訳](input.json) と [実行環境](environment.json) を保存した。

AMD EPYC 9V74、Linux x86_64、5 logical CPU、CPU quota 4、cgroup メモリ上限16 GiBで実行した。
`cargo build -p cli --locked` の dev profile、`opt-level=2`、Rust 1.95.0を使った。
バイナリを固定した別パスへ複製し、計測中にビルドやテストを並行実行していない。
各全体検査は、検証結果も分割ヒントも空の独立したキャッシュディレクトリから開始した。
分割まで180秒、実行全体は600秒で中断する条件で、`REF_TYPE_PROFILE_PROGRESS=1 REF_TYPE_PROFILE_PHASES=1` を指定した。
全体検査の各条件は1回ずつで、詳細計測のコストと実行ごとの揺れを含む。
最大RSSは supervisor と子孫の個々のプロセスの最大値で、同時点のプロセス全体の合計ではない。

## 既定条件の600秒

[計測結果](default.json) と [進捗の集計](default-progress.json) を保存した。
600.169秒で時間制限による中断となり、最終合否の JSON は生成されていない。
進捗上の完了は2,552 / 5,117で、対象本体の `cohomology_examples` にはまだ到達していない。
最大RSSは2,966,908 KiB、user time は581.771秒、system time は15.629秒だった。
CPU時間の合計は wall time の99.5%で、ほぼ1コアを使用している。

`Check` 完了イベントは11,321件、ユニークなモジュールは2,552個で、繰り返しは8,769件ある。
`std` は18回 `Check` され、`Skip` の再通知だけでは説明できない。
この比率はイベント件数であり、CPU時間の77.5%が重複したという意味ではない。
資源上限で後から中断された worker のイベントも含むため、この件数は最終的な検証成功の判定ではない。

最初の全体 worker は、category の検査を終えて保存中に約80秒で上限に達し、package ごとの検査へ分割された。
その後は `singular_excision`、`MayerVietoris.Over.On`、`GoodPair.On` などでさらに分割が起きた。
最後の進捗時刻598.462秒までの、重ならない phase の内訳は次のとおりである。

| phase | 秒 |
| --- | ---: |
| Checking | 463.878 |
| Saving | 53.020 |
| Cache | 52.040 |
| Loading | 16.744 |
| Planning | 9.044 |
| Restoring | 3.511 |

phase の切り替わりがない末尾の約1.7秒と初期化は、この集計に配賦していない。
worker 内の `phase=...` は包含関係があるため、この表には加算していない。

## メモリ上限8192 MiBとの比較

[8192 MiBの結果](eight-gib.json) と [進捗の集計](eight-gib-progress.json) も、600秒で未完了だった。
両方とも `cohomology_examples` 本体の検査に入る前である。

| worker の仮想メモリ上限 | 経過秒 | 進捗上の完了 / 5,117 | Check イベント | 重複 Check | 最大RSS KiB |
| --- | ---: | ---: | ---: | ---: | ---: |
| 3072 MiB | 600.169 | 2,552 | 11,321 | 8,769 | 2,966,908 |
| 8192 MiB | 600.195 | 2,964 | 8,580 | 5,616 | 4,758,776 |

8192 MiBでは `std` の検査が10回になり、`singular_excision` の追加分割を回避して `cohomology_models`、`derived_functors` へ進んだ。
ただし、最初の全体 worker は180秒の制限で分割された。
1秒間隔の `/proc` 観測では、この worker の最大RSSは約4.54 GiB、最大仮想メモリは約6.02 GiBで、8192 MiBの上限には達していなかった。
最終的に保存された [分割ヒント](layouts.json) は3072 MiBが7範囲、8192 MiBが全体の1範囲だった。
最初の worker のメモリ観測は [worker-observations.json](worker-observations.json) に残した。
メモリの増量は一部の再試行を減らすが、時間による分割と依存環境の再構築は残る。
完了モジュール数にはコストの異なるモジュールが混在するため、2,964 / 2,552を全件検査の高速化率とは解釈しない。
中断時に実行用の一時キャッシュが削除されるため、レポートの `cache_bytes` は終了後に残った分割ヒントの量である。

## 完了する範囲の個別計測

module と `--module-only --no-cache` を指定し、その宣言と参照先を検査した。
8192 MiB、180秒上限で、全体検査とは保存処理や依存範囲が異なる。
いずれも受理され、`verification_reused=false` だった。

| 選択した module | 通常計測 | 最大RSS KiB | 詳細計測 |
| --- | ---: | ---: | ---: |
| `cohomology_examples.Graph.On.With` | 3.999、3.860、4.120秒、中央値3.999秒 | 718,584 | 4.039秒 |
| `singular_excision.MayerVietoris.Over.On.Chains` | 8.136秒、1回 | 1,043,672 | 8.878秒 |
| `cohomology_examples.Torus.Geometry.Ring.Primitive` | 92.376秒、1回 | 6,014,584 | 111.992秒 |

[Graph](graph.json)、[Graphの詳細](graph-profile.json)、[Chains](chains.json)、[Chainsの詳細](chains-profile.json) に記録した。
詳細計測の group ごとの排他的時間は、Graph で source 1.169秒、query 1.056秒、kernel 0.799秒、namespace 0.063秒だった。
Chains では source 1.211秒、query 1.813秒、kernel 3.237秒、bridge 0.868秒、namespace 0.643秒だった。
各値は詳細計測の追加コストを含む。
小さな範囲でも source の読み込みと計画に一定のコストがあり、結果だけを再利用する worker の起動回避には改善余地がある。
この2つの範囲の内訳を、全5,117モジュールのCPU時間の内訳へ一般化はできない。

[Torus](torus.json) の詳細は [torus-profile.json](torus-profile.json) に保存した。
詳細計測の排他的時間は namespace 50.104秒、kernel 33.444秒、query 11.878秒、bridge 8.723秒で、namespace が計測時間の約44.7%を占める。
通常計測92.376秒に対し、詳細計測は111.992秒なので、内訳を通常計測の秒数へそのまま加算しない。

| Torus の処理 | 呼び出し回数 | 排他的時間 |
| --- | ---: | ---: |
| `namespace.bind` | 27,870 | 21.317秒 |
| `namespace.substitute-arguments` | 8,116,929 | 9.366秒 |
| `namespace.check-shareability` | 8,386,641 | 8.507秒 |
| `namespace.reuse-definition` | 7,014,447 | 6.045秒 |

frontend の新規特殊化を表す `namespace.definition-fresh` は3,722,640件で、既存特殊化の exact hit も3,291,093件あった。
本体の遅延化・共有に加え、各宣言のメタデータ予約、引数の置換・intern・共有可否の処理が残っている。

別に Graph を `perf record -e cpu-clock:u -F 99 --call-graph dwarf,8192` でも計測し、423サンプル、lost 0、受理を確認した。
[計測](graph-perf.json) と [symbol集計](graph-perf-symbols.json) を保存した。
この短い入力の少数サンプルは補助的な観測とし、上記の内訳は cost scope の排他的時間を使う。

## コードから確認できる再構築の条件

[supervisor](../../../src/cli/src/supervisor.rs) は full check の worker に `narrow_environment=true` を指定する。
その実行専用の空の保存先を使うため、実行前の検証結果は再利用しない。
[prefix の選択](../../../src/sema/src/packages/native.rs) は、必要範囲外のモジュールを含む広い環境をこの条件で拒否する。
一方、保存される prefix は `PackageChecker::checkpoint()` による、その時点の resolver と checker 全体である。
先行 package の独立した宣言を含む prefix は、後続の狭い依存閉包には適合しにくい。
結果だけが再利用できても、新しい宣言の検査に必要な環境を再構築する際に、既に検査した依存が再び `Check` される。

分割済みの各 worker は snapshot 全体を読み込み、4,105ファイルを parse する。
実際に新しい宣言を検査せず、結果を再利用して終了する worker でも、この起動・計画コストが発生していた。

## 改善案

1. **同じ実行内の検査済み環境を、依存閉包ごとに共有する。**
   `prefix_score` の広い環境をそのまま復元する方法に加え、必要な宣言と参照先だけを取り出す仕組みを用意する。
   resolver、raw/kernel の式、名前空間、完了範囲を整合した単位で切り出し、共通部分を共有する。
   `--full-check` が開始した後の検査結果であることを実行単位で識別する。
   評価指標は、繰り返し `Check` 件数、全体時間、最大RSS、全件の受理結果である。

2. **名前空間のメタデータと引数処理を減らす。**
   [namespace の具体化](../../../src/elaboration/src/elaborator/module_manager.rs) には、既に namespace-instance cache と宣言本体の遅延化がある。
   この共有をメタデータ予約まで広げ、参照された宣言から具体化する案を評価する。
   より小さい変更として、intern 済みの引数IDと共有可否を namespace や予約グループで保持し、宣言ごとの引数処理を減らす。
   nominal ID、局所文脈、Program の区別を維持する。
   評価指標は、Torus の92.376秒、namespace の排他的時間、新規特殊化件数、最大RSSである。

3. **分割と再試行を、進捗とメモリ使用量に合わせる。**
   既定条件では最初の全体試行がメモリ上限に達し、その後も親範囲から子範囲への再構築が続いていた。
   既存の分割ヒントに加え、初回の計画で大きな依存閉包を識別し、不要な親範囲の試行を減らす。
   時間で分割する際も、直近に完了した検査を引き継げる境界を使う。
   評価指標は、破棄した worker のCPU時間、分割回数、同じ進捗に到達する時間である。

4. **結果だけで回答できる分割範囲は、supervisor 側で処理する。**
   現在の cache probe は保存済みの分割に対する通常検査を主に扱う。
   full check の実行中に生成した、検証済み manifest の coverage を軽量に保持し、既に完了した範囲のための worker 起動を減らす。
   判定には実際に保存された検証結果を使い、途中の進捗イベントを検証済みの証拠として扱わない。
   評価指標は、検査をしない worker の数と Loading / Planning / Cache の合計時間である。

これらの処理系の変更は未実装で、全体の短縮率はまだ測っていない。

## 再現

```sh
cargo build -p cli --locked
bash benchmarks/records/cohomology-examples-full-check/measure.sh target/debug/cli
```

`FULL_SECONDS` で全体検査の時間上限を変更できる。
各条件のログ、キャッシュ、通常のレポートは `benchmarks/runs/cohomology-examples-full-check/reproduce-*/` に保存する。
`summarize.py` は途中で中断したレポートからも進捗件数と phase の内訳を集計する。
perf の観測は、通常計測と別に次のように再現できる。

```sh
perf record -e cpu-clock:u -F 99 --call-graph dwarf,8192 -o benchmarks/runs/graph-perf.data -- \
  python3 benchmarks/bench.py run libs/topology/examples/finite_models \
  --runs 1 --cache-mode off --memory-mib 8192 --seconds 180 \
  --module cohomology_examples.Graph.On.With --extra --module-only
perf report -i benchmarks/runs/graph-perf.data --stdio --no-children --no-inline \
  --call-graph none --comms cli,exe --sort symbol
```

このディレクトリの計測 JSON は、元のレポートから大量の個別 phase 配列だけを省いたもので、コマンド、digest、資源制限、終了状態を保持する。
バイナリ、詳細ログ、キャッシュはコミットに含めていない。

## 記録の確認

benchmark runner の6テスト、再現スクリプトの `bash -n`、JSON の整合性確認が成功した。
全計測で入力とバイナリの digest が計測中に変わっていないことを確認した。
3つの個別選択範囲は通常・詳細計測とも受理され、検証結果の再利用は false だった。
