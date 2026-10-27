# 相対 K 群（K03、実装中）

B09 統合済み main `bd8fd86d5368968ff22e06f81beb5469bc348623` から、`math/k03-relative-k` / [Draft PR #50](https://github.com/pdf-jube-joba/ref-type/pull/50) で実装中。
[計画](../../../_plans/math/k03-relative-k.md)の全要件はまだ完成していない。

## 現在の API

入口は `relative_k_theory.Relative`。
`Pair.Quotient` は一点を付加してから閉部分空間とともに潰し、空の部分空間も同じ定義で扱う。
その被約 K 群、反復 suspension による負次数群、写像の引き戻しを構成した。
`Equivalence` は基点付き同値から各負次数の群の同型を作る。
`Pair.Excision` は開集合を閉部分空間から取り除いた対の商の同相と群の同型を提供する。

`Pair.Triple` は二つの射影表示と閉部分空間上の比較同型を持つ。
`Pair.Group` は全体に延長する同型・直和・合成・ホモトピーの関係式による群。
`SumConstruction` は直和を構成し、`Normalize` は補束の対角三つ組を加えて負側を自明化する。
`FromBundles` は一般の二つの束と境界上の同型から、元の束との比較を伴う三つ組を作る。

`Group.Forget` は正側と負側の差を通常の K 群へ送る。
`Pair.Restriction` は閉部分空間への制限。
`Group.Forget.Kernel` は忘却後の制限が零であること、`Group.Forget.Exact` は通常の K 群における像と核の一致を証明する。
`Pair.FromKernel` は制限先で消える射影表示の差を安定化し、その原像となる三つ組を構成する。

`Descent.descend` は境界上で自明化された束を商へ降ろし、元の束との引き戻し比較、基点のランク、境界上の整合式を返す。
`Pair.FramedMaps` と `FramedIsomorphisms` は境界の自明化と定数行列に両立する写像・同型を降ろす。
`FramedChoices` は近傍延長の選択によらない束の同型と被約群の元を提供する。
三つ組の群と商の被約群の全比較はまだ未完成。

## 検証と再開

共有キャッシュは `libs/refcache`。
以下の対象検査は accepted・終了0・キャッシュ保存失敗0で、報告・ログ・終了コードは `work/k03-resume` に保存した。

| 範囲 | 報告の接頭辞 |
| --- | --- |
| 三つ組の群、引き戻し、ホモトピー不変性 | `group-fixed` |
| 商の基点外の同相、降下のファイバーと枠 | `outside-batch-*` |
| 座標の読み書き、開被覆 | `coordinates-batch-Descent` / `cover-batch-*` |
| 降下した束と比較同型、存在とランク | `descent-comparison-fixed` / `descent-public-fixed` |
| 三つ組の直和と補束による正規化 | `triple-sums` / `triple-normalize` |
| 共通の有限列挙、Hausdorff 性、基点付き suspension | `common-ListIndex` / `common-Separation` / `common-pointed-fixed` |
| 局所行列による束写像、境界上一定の行列の降下 | `local-matrices-fixed` / `matrix-descent-fixed` |
| 枠と両立する束写像、近傍の選択独立性、被約群の元 | `framed-public` / `framed-choices-public` |
| 忘却・制限と生成元での零性、群全体での零性 | `exactness-linear` / `restriction-kernel` |
| 基点付き同値と切除の負次数群の同型 | `invariance-Equivalence` / `invariance-Excision` |
| 自明束の引き戻し、一般の束からの三つ組の表示 | `bundles-TrivialPullback` / `bundles-FromBundles` |
| 制限核の元の安定化と通常の K 群における完全性 | `kernel-FromKernel` / `kernel-Exact` |
| 三つ組の同型不変性と射影表示の選択独立性 | `change-Isomorphic` / `change-PresentationChange` |

`change-Isomorphic` と `change-PresentationChange` は accepted・終了0・キャッシュ保存失敗0。
最新の未検証変更は反復 suspension の同値の写像と通常の引き戻しの一致、および `Pair.FromQuotient`。
`FromQuotient` は商上の束の基点での局所枠を使い、引き戻した束と自明束の境界同型から三つ組を作る。
固定 snapshot は `work/k03-resume/from-quotient.source.json`。
次は `relative_k_theory.Relative.Equivalence`、`relative_k_theory.Relative.Pair.Excision`、`relative_k_theory.Relative.Pair.FromQuotient` を順に検査する。

検査には `--memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 --diagnostics compact` を指定する。
固定 snapshot、JSON 報告、実行シェルの終了コードを `work/k03-resume` に保存する。
古い `framed-outside` と `framed-outside-diagnostic` は終了130で中断した検査であり、後続の固定 snapshot の検査結果と区別する。

汎用の有限列挙・基点付き suspension・Hausdorff 分離を共通層へ移し、局所検査の依存閉包を縮小した。
移動元を含む K02・単体・胞体座標・近似理論・clutching の影響先は最終検査に含める。

残る主な要件は、三つ組の群と商の被約群の全比較、負次数までの長完全列、Mayer–Vietoris、外積と自然性、束の円板球面対への適用と具体例。
公開登録・ロードマップ・下流リンクと、package・依存閉包・影響先・workspace 全体の最終検証も未完了。
