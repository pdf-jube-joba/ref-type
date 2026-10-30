# A11 Fredholm 作用素と指数の検査記録

A11 の全要件を実装し、以下の最終ソースで対象・関連回帰・通常全体検査を完走した。
未完了項目と未検証範囲はない。

## 計画の達成状況

| 要件 | 実装 |
| --- | --- |
| コンパクト作用素のイデアルと Atkinson の同値 | `Operators.Ideal`、`At.Hilbert.atkinsonEquivalence`、`fredholmOfParametrix`、`parametrixExists` |
| 実際の核・余核の有限次元性 | `At.kernel`、`image`、`CokernelSpace`、`FixedSubspace`、`CompactQuotient` |
| 指数の合成則 | `At.Composition.Hilbert.indexComposition` |
| 指数の直和則 | `At.Hilbert.DirectSum.At.indexDirectSum`。直和の内積・ノルム・完備性・有界写像も構成する |
| コンパクト摂動不変性 | `At.Hilbert.CompactPerturbation.indexInvariant` |
| ノルム連続族での局所定数性 | `indexLocallyConstant` と `Operators.Hilbert.Family.At.locallyConstant`。パラメータ空間は任意の位相空間 |
| 実際の分解による指数の計算と利用例 | `At.Index.Decomposition`、`fromDecomposition`、`indexFromDecomposition`、`Examples` の実際の核・商余核の零次元基底と `indexZero` |

## ソースと処理系

- 検査ソース commit: `58f20c30015fd6d343ff3f77f8dcc7ec1240afc0`。
- 基点 main: `cfca188e66f15dfe8c354b18861a9920d12f83d5`。PR #59 を取り込み済み。
- release CLI SHA-256: `96e9f70c1924311a06c667b21dda6b71e3c0ad85299d570ee586b66d1f2d2820`。
- A11 の `.ref`・manifest・workspace manifest 90 ファイルの SHA-256: `941f5eb53c9a01043103b593551fbb2ab03ff6a83c1a7a3e3bbe891f8cfd41f3`。
- ハッシュは辞書順の `path + NUL + contents + NUL` を連結して計算した。
- 処理系ソースの差分はない。標準コマンドで再ビルドしたバイナリは対象検査のバイナリと同じ SHA-256 だった。
- この検査後のコミットは記録・公開 README・計画・履歴の文書更新のみで、数学ソースと manifest は変更していない。

## 対象と関連回帰

| 範囲 | 結果 / 終了コード | 経過秒 | 最大 RSS MiB | 再検査 module | 再利用 module | checkpoint 再開 |
| --- | --- | ---: | ---: | ---: | ---: | ---: |
| A11 全体 | accepted / 0 | 9.943 | 1100.7 | 88 | 617 | 1 |
| 具体例・隔離キャッシュ | accepted / 0 | 37.139 | 795.9 | 704 | 0 | 0 |
| A19 回帰 | accepted / 0 | 5.553 | 753.9 | 47 | 296 | 2 |

全コマンドと統計は [targeted-summary.json](targeted-summary.json) に保存した。
A11 全体検査の `checked_modules` を全 88 `.ref` と照合し、全ファイルを再検査したことを確認した。
各検査は worker 1、300 秒上限、CLI の既定メモリ上限で実行した。
対象検査を順に実行してから通常全体検査を開始し、両者は並行していない。
時間は各プロセスの起動から終了までの経過時間で、ビルド時間を含まない。
隔離キャッシュは空の `work/a11-final-isolated/` から開始し、再利用 module、result hit、checkpoint 再開がすべて 0 で具体例の検査が成功した。
保存失敗・不正なキャッシュ読み込み・worker 復旧はすべて 0 だった。

## 通常全体検査

```sh
source /workspace/ref-type-env.sh && cargo build -p cli --release --locked && python3 scripts/check_all.py
```

結果は **accepted、終了コード 0、9,887/9,887 対象を検証済み、未検証 0**。
新規検査 6,329、検証済み結果の再利用 3,558 だった。

- Cargo 表示の release ビルド時間: 1 分 34 秒。
- ビルドを含む標準コマンドの経過時間: 5874.754 秒。
- 全体検査ドライバの経過時間: 5780.496 秒。
- 意図的な停止時間: 0 秒。手動の中断と未完了範囲はない。資源制約による worker の停止・復旧時間は個別には計測しておらず、上の経過時間に含む。
- 検査の試行数: 129。初期メモリ上限 4608 MiB、上限 6144 MiB、キャッシュ予算 12288 MiB。
- 各子プロセスの最大値は RSS 5296.9 MiB、仮想メモリ 6112.7 MiB。全プロセスの同時合計ではない。
- checkpoint 再開 1、worker 復旧 4、保存失敗 0、不正なキャッシュ読み込み 0。

メモリ上限による試行は 21 回で、対象・上限・終了コードは `repository-summary.json` の `resource_limit_attempts` に残した。
`bott_product` の初回範囲は 4,608 MiB 上限で `memory-limit` / 2 となり、標準ドライバが宣言自身と子モジュールへ分割して検証を続けた。
分割できない宣言は設定済みの 6,144 MiB 上限へ引き上げて再試行した。
これは標準コマンド内の自動復旧で、キャッシュの全削除や全体検査の二重起動はしていない。
最終の coverage は全対象と一致し、資源制約で未検証のまま残した範囲はない。

実行場所は `/workspace/ref-type/work/repository-check/20261030T151047.992004Z/report.json`。
ソーススナップショット、対象集合のハッシュ、全試行の結果と資源上限は [repository-summary.json](repository-summary.json) に保存した。
既存の `libs/refcache/` と検証状態を利用し、全削除はしていない。
以前の実行とはキャッシュ条件が違うため、時間の比率を性能改善の計測値として扱わない。

## 特殊化の調査と回避

初期ソース `b947d8824e6de71444da94515bb889364720a352` では具体的な作用素への適用が失敗した。
[当時の対象診断](history/b947d88-target-failure.txt)、[当時の具体例診断](history/b947d88-examples-failure.txt)、[当時の通常全体診断](history/b947d88-repository-failure.txt) は歴史的な記録であり、上記の最終検査の失敗ではない。
旧 JSON は [当時の対象検査](history/b947d88-targeted-summary.json) と [当時の通常全体検査](history/b947d88-repository-summary.json) に分けて保存した。
余核の証明を作用素から独立した `CompactQuotient` へ分け、有限次元性の同型による移送を独立した補題にすることで解消した。
最終の具体例は Atkinson の両方向と指数の全法則を実際に特殊化する。

局所的に存在量化された添字で構造体をその場で作る別の処理系制限は、[inline 版](repro-inline.ref) と [補助モジュール版](repro-helper.ref) の std のみの単独例に切り分けた。
両方の `root.ref` を個別の一時 package に置き、`std = { path = "<checkout>/libs/std" }` を依存に持つ manifest で `target/release/cli <package> --no-cache --diagnostics compact --time-limit-seconds 120 --report-json <report>` を実行した。
inline 版は `DefinitionLocalContextIsOutsideReferenceScope` による worker panic 101、CLI 終了コード 2、補助モジュール版は accepted / 0。
型導出と現在の書き方は [gaps.md](../../../gaps.md) に記録した。
[repro-summary.json](repro-summary.json) に正確なコマンド、ソースハッシュ、検査統計を保存した。
この最小例はキャッシュ・checkpoint なしで再現するため、#59 の checkpoint 再開時の補助 import の修正だけでは解消しない。
内部原因の共通性は未確定で、A11 は処理系を変更せずに完成した。
