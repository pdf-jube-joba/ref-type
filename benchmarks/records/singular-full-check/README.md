# singular_cohomology の module 展開と全件検査

比較元は `4d8f20be8b24c60c9345a090c456671fbc86122e`、比較先はこの記録を追加する変更である。
`libs/` は変更せず、module の具体化と全件検査中の環境の引き継ぎを改善した。
既定条件で分割設定を使う全件検査は529.364秒から365.561秒へ短縮した。
メモリ上限8192 MiB、分割まで300秒の追加測定は255.865秒（約4分16秒）で完了した。

## 実装

論理的な宣言は、元の本文を明示的な捕捉引数付きで一度 lower する。
その本文の局所文脈で作った匿名 import を、呼び出し側の namespace ごとに再具体化する必要はない。
元の宣言を共有できる namespace 同士でこの展開を省き、名前付き import と Program の宣言は従来の具体化を使う。
module 引数の元の telescope を共有し、引数追加と環境 import 時に索引を無効化する。
具体化をまとめるキーは宣言の配列を借用し、数値 ID の索引には FxHashMap を使う。
宣言の置換表は親との合成を共有したまま整理し、全体を平坦化して複製する処理を避ける。

`--full-check` は選択範囲の依存閉包を使う。
同じ要求内で既に検査した範囲は動作中の環境に残し、後続 package のための再構築を減らす。
強制検査の指定と検証済み結果の判定は維持する。

## 条件

Linux x86_64、AMD EPYC 9V74、5 vCPU、約18 GiB RAM、Rust 1.95.0 で計測した。
両バイナリは `cargo build -p cli --locked` の dev profile（opt-level 2）でビルドし、計測中はビルドやテストを並行実行していない。
全体検査は module の指定なしで実行し、依存を含む全2361ソース module を選択する。
入力の digest は `809702dbbf7058bafc48a5f9c4605c314af716bf552274240f1e1b812b534c54` で共通である。
`REF_TYPE_PROFILE_PHASES=1` を指定し、時間と最大RSSは supervisor と worker を含む値である。
各条件は1回の観測であり、繰り返しの分散は測っていない。

既定条件は worker ごとの仮想メモリ上限3072 MiB、分割まで180秒である。
「初回」は成果物と分割設定の両方が空、「分割設定あり」はそれぞれのバイナリの初回検査が保存した設定を使う。
設定の内容は [layouts.json](layouts.json) の `before_learned_input` と `after_learned_input` に保存した。
`--full-check` の検証用キャッシュは実行ごとに独立し、すべての全体検査で `verification_reused: false` を確認した。
分割設定の再利用と、過去の検証結果の再利用は別である。

| 条件 | 変更前 | 変更後 | 変更後の最大RSS |
| --- | ---: | ---: | ---: |
| 初回、3072 MiB / 180秒 | 681.348秒 | 423.108秒 | 2879996 KiB |
| 分割設定あり、3072 MiB / 180秒 | 529.364秒 | 365.561秒 | 2159744 KiB |
| 初回、6144 MiB / 300秒 | — | 302.450秒 | 5825128 KiB |
| 初回、8192 MiB / 300秒 | — | 255.865秒 | 6375812 KiB |
| With の個別検査 | 17.817秒 | 14.294秒 | 1254632 KiB |

[初回の変更前](cold-before.json)、[変更後](cold-after.json)、[分割設定ありの変更前](before.json)、[変更後](after.json) に、コマンドと結果を保存した。
初回は37.9%、分割設定ありでは30.9%短縮した。
既定条件では4分に届いていない。
分割設定ありの比較は、検査処理の改善と自動的に保存された分割の違いの両方を含む。

分割後は広い保存環境を許可する [別案](broad-retries.json) も測り、453.210秒、最大RSS2337760 KiBだった。
この別案は変更前と同じ分割設定で開始し、開始時の設定を `layouts.json` の `broad_retries_input` に保存した。
分割設定も異なるため、365.561秒との差を環境の共有方法だけの差とは解釈しない。
最終実装には、365.561秒で完了した構成を採用した。

メモリ上限だけを6144 MiBへ増やした [試行](six-gib.json) は298.802秒だった。
初回と6144 MiB / 180秒の試行は、同じ最適化を含む clippy 修正前のバイナリである。
修正内容は既存の条件式とテストの match guard の書き換えで、分割設定ありの変更後は修正後のバイナリで測った。

最終バイナリでメモリ上限6144 MiB、分割まで300秒にした [検査](six-gib-long.json) は302.450秒だった。
180秒による分割を避けてもメモリ上限で全体の検査が分割され、約5分かかった。

メモリ上限8192 MiB、分割まで300秒の [検査](eight-gib.json) は255.865秒で完了した。
成果物と分割設定が空の状態から始め、分割なしで全体を検査できた。
最大RSSは約6.08 GiBで、過去の検証結果を再利用していない。
処理系の既定のメモリ上限と分割時間は変更していない。

```sh
cargo build -p cli --locked
target/debug/cli libs/topology/singular_cohomology --full-check --memory-mib 8192 --batch-seconds 300
```

[With の変更前](with-before.json)、[変更後](with-after.json) に個別検査の記録を保存した。

With では namespace の排他的時間が7.28秒から2.54秒になった。
定義の具体化要求（exact hit、origin hit、fresh の合計）は2192089件から781801件、置換表の所有 capacity の合計は9088689から3062278に減った。
局所文脈を伴う匿名 import は12293件の展開を省いている。

With の個別検査は `--module singular_cohomology.Relative.Equivalence.Over.On.With --module-only --no-cache` と、`REF_TYPE_PROFILE_COSTS=1 REF_TYPE_PROFILE_PHASES=1` で測る。
全体検査と詳細計測の条件が異なるため、時間を直接足し引きしない。

## 検証と再現

Rust workspace の375テスト、受理・拒否400ケース、benchmark runner の6テスト、fmt と workspace 全 target の clippy が成功した。
[通常検査](warm.json) は2回とも検証結果を再利用し、時間は1.5345秒（中央値）だった。
[生成 workload](cache.json) では、別の利用側、入口編集、推移依存編集、依存順変更、独立した依存の追加、checkpoint 保存後の中断と再開を確認した。
[利用側の cohomology_models](consumer.json) は、全件検査後のキャッシュを使った `--full-check-local` が118.338秒で成功し、外部依存の検証結果を再利用した。

全体検査の比較には、変更前後のバイナリを別名で保存してから次を実行する。

```sh
bash benchmarks/records/singular-full-check/measure.sh /path/to/before-cli /path/to/after-cli
```

レポートは `benchmarks/runs/singular-full-check/comparison-*/` に保存する。
このディレクトリの JSON は元のレポートから個別 phase の配列だけを省き、コマンド、digest、資源制限、終了状態、時間、RSS、集計値を保存している。
バイナリ、詳細ログ、キャッシュは `benchmarks/runs/` に置き、コミットには含めない。
