# K11 作業チェックポイント

この記録は実装途中の保存であり、K11 全体の完了・受理を表さない。
最新 main `4d92b63566b7170526442de2a2979b9f36d85ab0`（A04、B07、G04 を含む）を取り込んだ `codex/k11-k-thom` の作業を保存する。
K11 の計画ファイルは完了扱いにせず残している。

## 解消済みの型変換エラー

自明束の比較では、束同型から自動的に移送したコンパクト性・Hausdorff 性の証明項と、呼び出し側が指定した証明項が定義上一致しなかった。
`For.BundleIsomorphism` が終域の証明を明示的に受け取る API に変更し、実際の類と写像の比較を検査した。
さらに `For.Proofs` は、恒等写像の引き戻しと実際の束同型から、任意の二組の証明に対する Thom 類と写像の一致を証明する。
処理系のコードは変更していない。

## 通過した開発検査の抜粋

通常 release checker のキャッシュを有効にした対象別検査である。
開発用 snapshot は必要なルート宣言を絞ったものを含むため、最終の無加工ソースに対する対象・回帰・全体検査の代わりにはしない。
各段階のソースはその後も統合しており、表はチェックポイント全ソースの同時受理を意味しない。
`steps` は JSON 報告の `checking.checked_steps` である。

| 内容 | 報告 ID | steps |
| --- | --- | ---: |
| 自明束の類・外積表示 | `trivial-thom` | 1,442 |
| 指定した自明化の類 | `trivialized-thom` | 1,484 |
| 証明の選択からの独立性 | `for-proofs` | 1,338 |
| 自明右因子との積 | `fiber-trivialization3` | 1,705 |
| 実際の階数0の単位類 | `zero-normal4` | 996 |
| 実際の複素直線の Bott 類 | `line-global3` | 2,005 |
| 点上の階数増加の幾何 | `point-sum4` | 1,751 |
| 階数0の外積同型 | `external-zero2` | 1,120 |
| 階数1の外積同型 | `external-line` | 3,655 |
| 実際の補助束の二段階消去 | `native-cancellation3` | 4,776 |
| 左側の Clifford 再配置 | `tensor-stabilization3-small` | 431 |
| 右側の Clifford 再配置 | `tensor-right-stabilization5-small` | 516 |
| 切断次数と直和の階数上界 | `product-degree2` | 899 |
| テンソル作用素の加法性 | `tensor-additivity` | 38 |

[reports.json.gz](reports.json.gz) に元の受理報告を保存する。
保存時点の checker バイナリ SHA-256 は `eea3ef7507622c9395d83c0377f9d40c52b78dd02b558ead1db8a58cba092c63`。
[source-sha256.json.gz](source-sha256.json.gz) は保存時点の K11 の `.ref`・manifest・README と共有更新ファイルの SHA-256 である。

## 残作業

- 大域の有限複体、局所比較、実際のテンソル作用素と直和の Koszul 類の最終接続。
- `KoszulProduct.equation`、任意階数の `BottExternal`、一般の `For.Isomorphism` の接続と検査。
- 直接和・合成・実束の複素化の最終 API の統合検査。
- 固定した最新ソースの通常対象・回帰・全体検査と最終証跡。

未検査・接続中のファイルを含む。作業はこの保存後も継続する。
