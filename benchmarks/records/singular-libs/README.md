# singular のライブラリ分割と module 具体化

比較元は `1b59e3a1b549a86f5e1a59ca3d3361137e35aef1`、比較先はこの記録を追加する変更である。
処理系は固定し、ライブラリの module 構成と配置を変えた。
相対同値の係数付き module の個別検査では、定義の具体化要求が781801件から488624件へ37.5%減った。
一方、細分を含む従来の全範囲の検査時間は279.925秒から294.391秒で、全体の高速化は確認できなかった。

## module の構成

`Relative.Maps.Over.On.Integer` とその `With` は、相対鎖・余鎖の写像と誘導写像を扱う。
長完全列の可換図式、接続写像の自然性、比較定理を子 module の `Naturality` に分けた。
これにより、誘導写像だけを使う相対ホモトピー同値の検査では、全体・部分空間の余鎖と長完全列の図式を毎回具体化する処理が減る。
自然性を使う箇所は `Integer[].Naturality[]`、係数付きでは `Integer[].With[coefficients := coefficients].Naturality[]` を参照する。

| 個別検査の構成 | 時間 | 最大RSS | 定義の具体化要求 |
| --- | ---: | ---: | ---: |
| [変更前](before-with.json) | 14.471秒 | 1257644 KiB | 781801 |
| [試行A：係数付きの自然性を分離](trial-a.json) | 12.910秒 | 1156424 KiB | 595720 |
| [試行B：整数鎖の自然性も分離](trial-b.json) | 11.874秒 | 1077744 KiB | 488624 |
| [試行C：Bに加え鎖同値をまとめて双対化](trial-c.json) | 13.602秒 | 1131756 KiB | 528004 |
| [最終配置のB](after-with.json) | 12.425秒 | 1062232 KiB | 488624 |

試行Cは、相対鎖の同値を一度構成して `Hom.IntegerEquivalence` に渡す形を試した。
Bより検査が重く、定義と中間 module も増えたため、最終実装はBにした。
試行A・B・Cは配置変更前の探索時の観測である。
最終配置では変更前に比べて時間が14.1%、最大RSSが15.5%減った。
具体化要求は `namespace.definition-exact-hit`、`namespace.definition-origin-hit`、`namespace.definition-fresh` の合計である。
同一の処理系で件数が減っており、時間の揺れとは独立に不要な具体化が減ったことを確認できる。

## パッケージと配置

`SimplexChains`、`Subdivision`、`SubdivisionCells`、`Small`、`OpenCover` の5系列を新しい `singular_subdivision` に移した。
幾何的な細分・小鎖・開被覆の比較がこのパッケージに依存し、通常・相対理論とホモトピー不変性は `singular_cohomology` に残る。
頂点列上の一般的な細分 `OrderedTuples.Subdivision` も本体に残る。
本体から細分への依存はなく、本体の利用者はこれら5系列の全件検査を必要としない。

位相幾何の配置は次のように整理し、既存のパッケージ名は維持した。
依存パスと文書のリンクも更新した。

```text
libs/topology/
  basic/  metric/  constructions/  algebra/  homotopy/
  singular/
    cohomology/  subdivision/  excision/  products/  cech/  ...
  spheres/
  examples/
    cells/  cohomology/  finite_models/
```

全51パッケージの配置は [package-layout.json](package-layout.json) にある。
`singular_subdivision` を依存に追加した利用側では、移した5系列を `singular_subdivision.Small` などの名前で参照する。
依存閉包の module 一覧を対応付けた [module-inventory.json](module-inventory.json) では、従来の2361 module はすべて残っている。
新しいパッケージの root と `Naturality` の4 module が加わり、細分を含む全範囲は2366 module、本体の依存閉包は2245 module になった。

## 全件検査

| 検査対象と条件 | 時間 | 最大RSS |
| --- | ---: | ---: |
| [変更前の全範囲](before-full.json)、空のキャッシュ、8192 MiB / 300秒 | 279.925秒 | 6366376 KiB |
| [細分を含む変更後の全範囲](after-full.json)、空のキャッシュ、8192 MiB / 300秒 | 294.391秒 | 6277760 KiB |
| [変更後の本体](core-full.json)、空のキャッシュ、既定3072 MiB / 180秒 | 246.916秒 | 2869840 KiB |
| 変更後の本体、分割設定あり、既定3072 MiB / 180秒 | 219.610秒 | 2740440 KiB |

本体は初回約4分7秒、分割設定を再利用した再検査は約3分40秒である。
ただし、細分と開被覆の検査範囲を別パッケージに移した結果を含むため、従来の全範囲との同一作業量の比較ではない。
同じ数学的範囲を検査するには、変更後は `singular/subdivision --full-check` を使う。
この比較では5.2%遅く、module の具体化削減が全件検査の高速化に結びついたとはいえない。
環境のシリアライズ・圧縮の phase 合計も40.883秒から50.421秒へ増えた。
パッケージ境界による保存処理なども全体時間に影響するが、1回ずつの測定から原因の寄与は確定できない。

## 条件と検証

Linux x86_64、AMD EPYC 9V74、5 vCPU、約18 GiB RAMで計測した。
バイナリは比較元と同じ Rust ソースを `cargo build -p cli --locked` でビルドした dev profile（opt-level 2）で、SHA-256は `05ac53e50df108d34ba7e6aa64ae15155b002f322b8778cdd51778f6fcb16770` で共通である。
計測は直列に行い、ビルド・テスト・利用側の検査を並行実行していない。
各条件は1回の観測で、繰り返しの分散は測っていない。
本体の2回は空のキャッシュからの初回と、初回が保存した分割設定を使う再検査である。
性能比較に使った全件検査と個別検査はすべて `accepted`、`verification_reused: false`、入力とバイナリの変更なしを確認した。

全件検査では `REF_TYPE_PROFILE_PHASES=1`、Withの個別検査ではさらに `REF_TYPE_PROFILE_COSTS=1` を指定した。
個別検査は `--module singular_cohomology.Relative.Equivalence.Over.On.With --module-only --no-cache` を使う。
詳細計測と全件検査では条件が異なるため、両者の時間を直接足し引きしない。
JSONは元のレポートから個々のphase列とscope別の計測を省き、指定したphaseの合計・回数、具体化件数、コマンド、digest、終了状態を残した。
phaseには包含関係があり、合計を足して全体時間とは解釈しない。

受理・拒否400ケースが成功した。
workspace全体の module 列挙、全51パッケージの依存パス、文書内のローカルリンク、人間のnoteブロック18箇所の保持も確認した。

利用側の検査では、[3072 MiBでの切除](consumer-3gib.json) が `singular_excision.MayerVietoris.Over.On.Reduced.With.At` のメモリ上限で未完了になった。
利用側の検証は上限8192 MiB、分割まで300秒に切り替え、検証済みの依存・途中成果物を使う通常検査で続けた。
セル本体は12288 MiB / 600秒でも試行し、後述の複体の別名化の制約で停止した。
有限モデル全体は6144 MiB / 600秒で約15分検査して中断した。
この資源上限の変更は検証用で、処理系の既定値は変更していない。

単体的比較の依存先を未参照 module まで検査すると、`homological_algebra.Finite.Bounded.Mapping.At.With.TensorUniversalCoefficient.On` で型変換エラーになった。
比較元のcheckoutでも同じバイナリ・キャッシュなしの個別検査で再現し、今回の変更が入っていない依存閉包のソース・manifestも一致した。
コマンドと両方の診断は [preexisting-error.json](preexisting-error.json) にある。
このため、単体的比較以降は `--module singular_simplicial` などで利用側自身の全子 module と参照先を検査し、依存パッケージの未参照部分とは検証範囲を分けた。

球面の `Circle.Translations.degreeOne` でも、変更前のcheckoutで `\take` の結論が取り出した道に依存するというエラーを再現した。
返す等式を型付きの局所変数に置き、連続性の証明引数に由来する依存を結論の型から除くことで検査できた。
定理の結論と使う証明は同じである。
該当 module の変更前後の結果は [consumer-repair.json](consumer-repair.json) にある。
反転写像との一致を示す `Circle.Antipodal.Degree.translation` も、合同則の2引数を明示して単位円上の等式として検査できるようにした。
セルの `Disks.OneEdge.At.Data` は次元の等式の証明を引数に持ち、データを返す投影に `Prop` から `Set` への積が必要になっていた。
データ型から証明引数を外し、`fundamental` の法則でその証明を量化する形にした。
辺データを等式で運ぶ構成と接続写像の利用側も合わせて更新した。
`On.Layer.Retraction.Positive.map` の加法・スカラー倍の法則も、零拡張の部分型の引数を明示して適用する形にした。
`On.Cellular.With.complex` の署名型は、完全修飾名で直接書く形から、名前付き import を経由する形にした。
これは既存の [G16](../../../_plans/gaps.md#g16) の回避例と同じ方法である。
代表鎖の `At.Next.boundaryCycle` は帰納法で得た関数を現在の次数に適用するように直した。
零セルの写像と3箇所の接続・自然性の証明では、完全修飾した module の式を繰り返す形から、名前付き import を共有する形にした。
最終ファイルと全入力が一致する固定 snapshot 上で、零セルの `On.ZeroCollapse.Basis.Incidence.Connecting` の個別検査が成功した。
[結果](consumer-focused.json) には、もう一方の `On.CellCollapse.Pair.Basis.Incidence.Connecting` が変更していない親 `Pair.Basis.selected` の証明で停止した診断も残した。


以下の5パッケージは、自身の全 module と参照先の検査が成功した。
切除は module 指定なし、それ以外はパッケージ名を `--module` に指定し、子 module も含めた。
すべて上限8192 MiBで、キャッシュの状態が異なるため時間は性能比較に使わない。

| パッケージ | 自身のソース module 数 | 記録 |
| --- | ---: | --- |
| `singular_excision` | 87 | [結果](consumer-excision.json) |
| `singular_simplicial` | 187 | [結果](consumer-simplicial.json) |
| `sphere_maps` | 88 | [結果](consumer-spheres.json) |
| `singular_cellular_algebra` | 88 | [結果](consumer-cellular-algebra.json) |
| `cohomology_models` | 82 | [結果](consumer-models.json) |

セル全体の検査は、変更前と同じ本文の `On.Cellular.Representatives.Selected.integerMap` で複体の別名を通した型の変換に失敗した。
[結果と診断](consumer-cellular-blocked.json) は、既存の [G15](../../../_plans/gaps.md#g15) に対応する問題である。
写像をフィールドごとに組み立てる案と、引数を明示する案も試したが解消しなかったため、これらの試行は採用していない。
有限モデル全体の検査は [中断した記録](consumer-examples-interrupted.json) に残した。
これら2パッケージ全体の検査は未完了である。
有限モデルで今回参照を変更した接続写像の個別検査も、変更前と同じ本文の `ProjectivePlane.Geometry.Attachment.Base.attachingEquation` の型変換エラーで停止した。
[個別検査の診断](consumer-examples-blocked.json) に比較元との本文一致を記録した。

## 再現

変更前のcheckoutを用意し、現在と同じバイナリで比較する。
以下は空のキャッシュを毎回用意する全範囲の比較である。
今回の測定は空の共有キャッシュから開始し、本体の2回だけ同じ保存先を再利用した。

```sh
cargo build -p cli --locked
git worktree add --detach benchmarks/runs/singular-libs/before 1b59e3a1b549a86f5e1a59ca3d3361137e35aef1
singular_cli="$PWD/target/debug/cli"
singular_before="$PWD/benchmarks/runs/singular-libs/before"

REF_TYPE_PROFILE_PHASES=1 python3 benchmarks/bench.py run "$singular_before/libs/topology/singular_cohomology" --binary "$singular_cli" --runs 1 --cache-mode cold --seconds 1500 --memory-mib 8192 --batch-seconds 300 --output benchmarks/runs/singular-libs/reproduce-before.json --extra --full-check --cache-stats
REF_TYPE_PROFILE_PHASES=1 python3 benchmarks/bench.py run libs/topology/singular/subdivision --binary "$singular_cli" --runs 1 --cache-mode cold --seconds 1500 --memory-mib 8192 --batch-seconds 300 --output benchmarks/runs/singular-libs/reproduce-after.json --extra --full-check --cache-stats
```

本体の2回は、新しい空の保存先を指定して次のように測る。

```sh
REF_TYPE_PROFILE_PHASES=1 python3 benchmarks/bench.py run libs/topology/singular/cohomology --binary "$singular_cli" --runs 2 --cache-mode shared --cache-dir benchmarks/runs/singular-libs/reproduce-core-cache --seconds 1500 --memory-mib 3072 --output benchmarks/runs/singular-libs/reproduce-core.json --extra --full-check --cache-stats
```
