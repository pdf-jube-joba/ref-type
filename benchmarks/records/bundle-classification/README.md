# B06 束の分類写像と安定化の通常検査

基準 main は `5d213f86a635f17f309f058d929002e2840f393b`、実装ブランチは `feat/b06-bundle-classification`。
初回の実装は `libs/geometry/bundle_classification` の111 source module と package 登録、利用例、文書に限定する。
既存数学ライブラリと Rust 処理系のソース変更はない。

2026-10-30 のクラウド環境で、コンテナのメモリ上限16 GiBを確認した。
対象 package は初期・最大仮想メモリ10240 MiB、通常全体検査の最終実行は12288 MiBで行った。
通常検査は単一 worker、キャッシュ予算12288 MiB、空き容量目安256 MiBで行う。
通常の検証済みキャッシュと checkpoint を照合して再利用する。

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked
python3 scripts/check_all.py libs/geometry/bundle_classification --state-dir work/b06-package --initial-memory-mib 10240 --memory-mib 10240 --cache-budget-mib 12288 --min-free-mib 256
python3 scripts/check_all.py --state-dir work/b06-whole --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 256
```

対象を列挙して固定した source snapshot に対して検査し、終了時に source・対象一覧・処理系の一致を確認する。
実行ログ、全対象、source snapshot、各 package のレポート、最終集計は各 state directory に保持する。

## 結果

検査した実装コミットは `340f93e81ffcebf4673cbb9d57b2f8d388a61821`。
release build、対象 package と依存、通常全体検査はいずれも終了コード0で成功した。
機械可読の集計は [summary.json](summary.json) に保持する。

| 実行 | 対象数 | 新規検査 | 再利用 | 保存失敗 | 破損読み込み | 秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 対象 package と依存 | 5028 | 4912 | 116 | 0 | 0 | 437.839 |
| 通常全体、12 GiB | 10234 | 88 | 10146 | 0 | 0 | 464.575 |

対象 package の最大 RSS は2227236 KiB、最大仮想メモリは2645940 KiB。
通常全体の最大 RSS は9772424 KiB、最大仮想メモリは11559720 KiB。
全体の最終実行は checkpoint を1回再開し、worker の異常終了からの復旧は0回だった。
最終 checkpoint は33881で、保存失敗・入力不一致・キャッシュ破損は0だった。
コンテナの `memory.events` で `oom=0`、`oom_kill=0` も確認した。

初回の全体検査は10240 MiBで行い、10104対象を検証したところで、既存 `periodic_k_theory` の worker が仮想メモリ上限に2回到達した。
これは型エラーや処理系 panic ではなく、割り当て上限による復旧である。
checkpoint 32514、32529を保存して再開したが、進行が小さかったため driver を正常に中断し、同じ state directory を12288 MiBで再開した。
初回の outcome は `interrupted` であり、成功実行には数えない。
中断 package の詳細レポートでは復旧2回、checkpoint再開2回、保存失敗0、破損0を確認した。
中断 package は集計の完了済み attempts に含まれないので、初回の集計値だけから復旧数を判断しない。
キャッシュの全削除や検査の迂回は行っていない。

対象 package の source snapshot 全4266ファイルと通常全体の全9047ファイルを、`git cat-file --batch` による実装コミットの blob と照合し、差異0を確認した。
対象 package の report の commit 欄は snapshot 取得時の基準 main だが、その入力ソースは実装コミットと完全一致する。
両実行とも driver の終了時に現在の source・対象一覧・処理系の一致検査を通過した。
処理系の SHA-256 は `d6733af31783de12abb23e32a6e5f09130ce24511bfa1ef6a8008b47c749a944`。
通常全体の source SHA-256 は `0eeb1bb9f0e8e2ef45b0e98a8adc2677aeae4c24d1b5fcd404e54b9847b268eb`。

実行記録のローカル保存先は次の通り。

- 対象 package: `work/b06-package/20261030T225816.133680Z/report.json`
- 中断した初回全体: `work/b06-whole/20261030T230638.789689Z/report.json`
- 成功した最終全体: `work/b06-whole/20261030T234625.221490Z/report.json`

大きな source snapshot と package ごとの生レポートはローカルに保持し、Git には小さな集計と実行条件を記録する。

## G01 統合後の検査

2026-10-31 に G01 が入った main `78964e77017c7ed60d301540c94bcb74604edf39` を、マージコミット `189529e003defb213ee77fe79d94c1de4e176bfd` で統合した。
`libs/ref.toml` と `libs/README.md` は競合なく自動マージされ、G01・B06 の登録が一意であることを確認した。
G01 の実装・計画・検査記録・`gaps.md` は main と同一で、B06 の処理系・検査 driver への変更もない。

追加の自然性 API と利用例を含む最終ソースは `29aeab7f1c5a0e1e57d49d8aa7c0945739739faf` で、B06 の source module は122となった。
枠付き分類の商上の直和・安定化・引き戻しと分類 API を接続した。
向き付き直和・安定化については、元の直和束に与えた向きの輸送と分類との可換性を追加した。
当該コミットの比較は因子の向きから標準の積向きを生成する構成を含まない。
その後の標準の積向きの実装と検査は次節に記録する。
正確な API と入力は package README に記載する。

release build、追加 API の参照検査、対象 package と通常全体検査はいずれも終了コード0で成功した。
機械可読の集計は [integration.json](integration.json) にある。
通常検査は上記と同じ state directory・検証済みキャッシュを使い、初期・最大仮想メモリ12288 MiBで実行した。

| 最終ソースの実行 | 対象数 | 新規検査 | 再利用 | 保存失敗 | 破損読み込み | 秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 対象 package と依存 | 5039 | 0 | 5039 | 0 | 0 | 50.943 |
| G01・B06 を含む通常全体 | 10355 | 186 | 10169 | 0 | 0 | 170.062 |

追加 API は先行する参照検査で型検査され、通常 package 検査は照合された結果を再利用した。
両通常実行とも worker 復旧0、checkpoint再開0で、全 CLI attempt の終了コードは0だった。
通常全体の最大 RSS は1234984 KiB、最大仮想メモリは2118020 KiBだった。
対象 package の全4277ファイル、通常全体の全9168ファイルを実装コミットの Git blob と比較し、差異0を確認した。
両実行の終了時に source・対象一覧・処理系の一致検査も通過した。
処理系の SHA-256 は初回検査と同じである。
通常全体の source SHA-256 は `705b1fefc1b013c3f4ae9cb3d7c4a78ac3b78f74cf561428b521bf48e14e64b6`。
検査後の記録コミットは本 README と `integration.json` のみを更新し、検査済みソースを変えない。

- 対象 package: `work/b06-package/20261031T030049.831651Z/report.json`
- 通常全体: `work/b06-whole/20261031T030201.849003Z/report.json`

## 標準の向き付き直和と安定化の完成後の検査

有限次元の行列式積の証明を `ac4e480684aff0a8118323ab2646d9d9fb634ece` に、標準の積向きと自然性・連続性・利用例を `bdc5c32d9639d5764aa286b8f1fdfebf96d83425` に実装した。
後者が今回の最終検査ソースで、B06 は171 source module となった。
機械可読の最終集計は [standard.json](standard.json) に保持する。
以前の `integration.json` の未実装表示は旧検査コミット `29aeab7f1c5a0e1e57d49d8aa7c0945739739faf` に対する履歴である。

`Classification.DeterminantProduct` は左右に分離した引数上の評価で特徴付けた最高次形式の存在・一意性を証明し、基底の選択に依存しない双線形な行列式積を構成する。
`Laws` は非零性、`Mapping.naturality` は線形写像との整合性、`Blocks.blockDeterminant` はブロック対角写像の行列式の積公式を与える。
`Oriented.WhitneySum.orientation` は因子の向きと階数から直和の標準の向きを構成する。
`Open.open` と `Pairing.continuous` は局所自明化での係数の積から開性と行列式束の積の連続性を証明する。
`Mapping.With.preserves`、`Pullback.naturality` は向きを保つ因子同型と底空間写像への自然性を、`Classifying.WithSum.naturality` / `homotopy` と二つの `Changing` API は分類・選択独立性を公開する。
`Oriented.Trivial.orientation` と `Oriented.StandardStabilization` は標準の向き付き自明束の付加を扱う。
直和束全体の向きを前提とせず、階数0も含む。
利用例は `Classification.Examples.Trivial.Naturality.Oriented` にある。

release build と、最終ソースに対する通常対象・全体検査はいずれも終了コード0で成功した。
初期・最大仮想メモリとキャッシュ予算は12288 MiB、空き容量目安は256 MiBで、同じ state directory の検証済みキャッシュを再利用した。

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked
python3 scripts/check_all.py libs/geometry/bundle_classification --state-dir work/b06-package --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 256
python3 scripts/check_all.py --state-dir work/b06-whole --initial-memory-mib 12288 --memory-mib 12288 --cache-budget-mib 12288 --min-free-mib 256
```

| 最終ソースの実行 | 対象数 | 新規検査 | 再利用 | 保存失敗 | 破損読み込み | 秒 |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 対象 package と依存 | 5088 | 173 | 4915 | 0 | 0 | 71.039 |
| G01・B06 を含む通常全体 | 10404 | 0 | 10404 | 0 | 0 | 170.443 |

全 CLI attempt は終了コード0で、worker 復旧・checkpoint 再開は両実行とも0だった。
対象 package の最大 RSS は2125892 KiB、最大仮想メモリは2383828 KiB、通常全体はそれぞれ1241112 KiB、2118012 KiBだった。
新規 API の参照検査と通常対象検査で検証された結果が、最終全体検査で健全に再利用された。
キャッシュの削除や型検査の迂回は行っていない。
対象入力4326ファイルと全体入力9217ファイルを最終ソースコミットの Git blob と照合し、差異0を確認した。
両実行は終了時の source・対象一覧・処理系の一致検査を通過した。
処理系 SHA-256 は初回検査と同一、通常全体の source SHA-256 は `83e29833c2bcff8fb754d099c3e72452aee538c20351ad4ac9620ce5ebcc677d` である。
G01 の実装・計画・検査文書と `gaps.md` は統合 main と同一で、既存数学ライブラリ・Rust 処理系・検査 driver の変更はない。
検査後の記録コミットは本 README と `standard.json` のみを更新し、検査済みソースを変えない。

- 対象 package: `work/b06-package/20261031T040244.053085Z/report.json`
- 通常全体: `work/b06-whole/20261031T040532.284730Z/report.json`
- Git blob 照合: `work/b06-standard-source-commit-match.json`
