# 相対 K 群（K03、実装中）

B09 統合済み main `bd8fd86d5368968ff22e06f81beb5469bc348623` から、`math/k03-relative-k` / [Draft PR #50](https://github.com/pdf-jube-joba/ref-type/pull/50) で実装中。
[計画](../../../_plans/math/k03-relative-k.md)の全要件はまだ完成していない。

## 現在の API

入口は `relative_k_theory.Relative`。
`Pair.Quotient` は一点を付加してから閉部分空間とともに潰し、空の部分空間も同じ定義で扱う。
反復 suspension による負次数群、引き戻し、基点付き同相からの各負次数の比較、開集合を閉部分空間から取り除く切除を提供する。

`Pair.Triple` は二つの射影表示と閉部分空間上の比較同型を持つ。
`Pair.Group` は全体に延長する同型・直和・合成・ホモトピーの関係式による群。
`SumConstruction`・`Normalize`・`FromBundles` は直和、負側の安定自明化、一般の束からの三つ組を構成する。
`Group.Forget` は正負の差を通常の K 群へ送り、`Pair.Restriction` は閉部分空間への制限を与える。
`Group.Forget.Exact` と `Pair.Exact` はこの位置での像と核の一致を示す。

`Descent.descend` は境界上で自明化された束を商へ降ろし、元の束との引き戻し比較と基点のランクを返す。
`FramedClass`・`FramedSum`・`BundleSwitch` は枠付き束の選択独立性、加法性、安定化、ホモトピー不変性、境界同型に沿う交換を構成する。
`Pair.Comparison` は三つ組の群と商の被約群との両方向の準同型と左右の逆の等式を公開し、比較同型の対象検査を完了した。
`Pair.ForgetProjection` は忘却が商への射影による引き戻しに一致することを示す。

`Pointed.Cofiber` は、底面と閉部分空間の円柱の和を潰してコンパクト Hausdorff cofiber を作る。
円錐像の閉埋め込みと収縮、円錐像を潰した商と元の相対商との比較は対象検査済み。
`BaseQuotient` は底面を潰した商と部分空間の suspension を、連続な明示的逆写像によって比較し、対象検査を完了した。

## 追加と検証状況

基点が部分空間に含まれる対の `Connecting`・`Rotation`・`LeftExact`・`FiveTerm` は対象検査を完了した。
`SuspendedPair` の閉埋め込みと商の suspension との比較も対象検査を完了した。
`ClosedPointedPair`・`PointedPair`・`PairIteration` は対を反復し、全体・部分空間・相対商の比較、包含と射影の可換性、各負次数の列を構成する。
`PairMapping.Iteration` は対の写像を反復し、比較写像との可換性を帰納的に示す。
`PairMapping.Naturality.Negative` と `PairMapping.Iteration.Naturality` は制限・忘却・接続写像の自然性を構成するが、対象検査は未完了。

## 検証と再開

共有キャッシュは `libs/refcache`。
以下の固定 snapshot の対象検査は accepted・終了0・キャッシュ保存失敗0。
現在の package・依存閉包・影響先・workspace 全体の最終検証は未実施。
報告・ログ・終了コードは `work/k03-resume` に保存している。

| 範囲 | 報告の接頭辞 |
| --- | --- |
| 三つ組と商の全比較同型 | `reduced-retraction-*` |
| 商の被約群側の忘却・制限の完全性 | `sequence-foundations-Pair-Exact` |
| 負次数の恒等・合成則、定数写像、三つ組の表示 | `sequence-ordered-*` |
| 収縮可能な閉部分空間での忘却の単射性と比較 | `contractible-kernel` / `contractible-forget` / `contractible-comparison-*` |
| コンパクト cofiber と連続な全単射からの同相 | `compact-cofiber-*` |
| 円錐像の閉埋め込み、同相、収縮 | `cone-image-*` |
| 円錐像を潰した商と元の相対商の比較 | `cone-quotient` |
| 枠付き束の降下の引き戻し計算 | `forget-projection-Pair-FramedClass-With-Pullback` |
| 忘却と射影の引き戻しの一致、基点付き被約群の完全性 | `direct-inverse-Pair-ForgetProjection` / `direct-inverse-Pair-Pointed-Exact` |
| 束写像の剪断、交換、直和の並べ替え | `shears-*` / `reordering-*` |
| 底面の商の raw 写像・一意性・連続性 | `subset-raw` |
| 底面の商と suspension の比較全体・明示的な逆・忘却の式 | `subset-comparison` |
| 接続写像・相対群での完全性（module 自身と依存先） | `forget-square-connecting` |
| 二段目の接続写像の候補像と核（module 自身と依存先） | `forget-square-left-exact` |
| 変形の内部・全体・両端、suspension の制限の完全性、基点付き五項の列 | `rotation-stage-*` |

検査を中断した旧報告は `outcome=interrupted`・終了130として保存し、成功した検査とは区別している。
検査中に見つかった親参照、部分空間の点の型推論、large elimination の不一致を修正した。
二つの忘却写像は射影の引き戻しへ比較して結び、その修正を含む五項の列を検査した。

現在の検査は `iteration-foundations.source.json` を固定して順番に実行する。
`SuspendedPair` 自身とその `Quotient` 全体は accepted・終了0・保存失敗0。
`PointedPair` も accepted・終了0・保存失敗0。
`PairIteration` の検査は最初の反復定義の module 参照を拒否した（終了1・保存失敗0）。
ルートからの参照を明示し、`iteration-qualified.source.json` で `PairIteration` と `PairIteration.Sequence` を再検査する。
この snapshot は検査済みの `forget-square` に反復部分の修正を加えたもので、後述の追加全体は含まない。
プロセスが残っていれば重複起動せず、`work/k03-resume/iteration-stage-*.{log,json,exit}` を確認する。
終了時は終了コード・JSON の `outcome`・`storage.save_failures`・`checking.cache_write_failures` を確認する。

自然性の追加は `negative-boundary-naturality.source.json` まで構文解析を通過した。
その後 `Absolute.Mapping.Naturality` に通常の K 群との比較の自然性を書いた（未検証）。
次の追加は型検査未完了で、現在の package 全体の最終検証も未実施。

- `KTheory.On.Empty`、空の境界での三つ組の忘却の逆写像、`Absolute` の一点付加と通常の K 群との比較。
- `Pair.Augmented.Sequence`・`OrdinaryEnd` の一般の対の列、通常の忘却・制限との一致。
- `Pair.Mapping.Based`、`PairMapping`、`Square` の写像と自然性。
- `Pair.ClosedCover` の商の比較、`MayerVietoris` の境界写像と全体の群での完全性。
- `DiskPair`・`BundleDisk` の円板球面対、元の束への連続単射とノルム条件、`Examples.TrivialDisk` のランク0・1の例。

残る構成は一般の対での自然性、Mayer–Vietoris の残る位置での完全性、外積と自然性。
検査完了後、公開登録・ロードマップ・下流リンクを整備する。
K02・K07・単体/胞体・近似理論・B09 の影響先と workspace 全体を最終検証に含める。
