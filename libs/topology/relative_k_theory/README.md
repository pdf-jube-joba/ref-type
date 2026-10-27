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
反復 suspension の同値の写像と通常の引き戻しの一致、および切除の写像の一致は `quotient-Equivalence`・`quotient-Excision` で検査済み。
`Pair.FromQuotient` は局所枠の証明を持つ表示の型を修正し、再検査する。
`Pair.BundleChange` は元の二つの束と境界同型をともに取り替えたときの群の元の一致を証明する。
共通の `Operations.Over.TrivialMap` と `TrivialIsomorphism` は定数の線形写像・同型から自明束の写像・同型を作る。
これらの対象検査は `bundle-change-*` ですべて accepted・終了0・キャッシュ保存失敗0。
`QuotientIsomorphisms`・`QuotientClass` と `BundleGlobal` は `quotient-class-*` で対象検査済み。
最新の未検証変更は `QuotientTrivial`・`QuotientAdditivity` と共通の `GlobalFrame`。
前者は自明束の零性と直和の加法性、後者は空間全体を覆う局所枠から自明束への同型を作る。
`QuotientClass` は商上の束から三つ組の群の元を一意に定め、束の同型で保たれることを示す。
`BundleGlobal` は境界同型が全体の束の同型に延びる場合の零性を示す。
`FromQuotient` は商上の束の基点での局所枠を使い、引き戻した束と自明束の境界同型から三つ組を作る。
`GlobalFrame` と `QuotientTrivial` は `quotient-additive-fixed-GlobalFrame`・`quotient-additive-fixed-QuotientTrivial` で検査済み。
`QuotientAdditivity`・`FromReduced`・`Reconstruction` は `reconstruction-*` ですべて accepted・終了0・キャッシュ保存失敗0。
`FromReduced` は同型類と群完成を経て商の被約群から三つ組の群へ写す。
`Reconstruction` は各三つ組を正規化して商へ降ろした束の差が、元の三つ組へ戻ることを示す。
`Group.Induction`・`Surjectivity`・`BundleModel`・`FramedBundles` は `framed-bundles-*` ですべて accepted・終了0・キャッシュ保存失敗0。
`Group.Induction` は和と逆元に関する帰納法を整数作用から証明し、`Surjectivity` は各三つ組の復元を群全体へ拡張する。
一般の束に対する写像の本体は `FramedBundles` に移し、射影表示の `FramedMaps` はその入口として残した。
`BundleModel` は基底位相を明示した束のデータを持つ。
`FramedBundleIsomorphisms`・既存の `FramedChoices`・`FramedClass`・`TripleClass` は `framed-class-*` ですべて accepted・終了0・キャッシュ保存失敗0。
`FramedClass` は一般の境界自明化された束について近傍延長の選択によらない被約群の元を定め、全体の枠へ延長する場合の零性を示す。
`TripleClass` は三つ組に負側の補束を加えてこの構成を適用する。
`TripleClass.Global` は全体に延びる比較同型の零性を示す。
`FramedClass.To` と `CylinderNeighborhood` は `framed-natural-fixed-To`・`framed-natural-fixed-CylinderNeighborhood` で accepted・終了0・キャッシュ保存失敗0。
前者は枠と両立する束の同型と座標同型に対する被約群の元の不変性。
後者は閉部分空間上の円柱全体と時刻0を含む開近傍内に入り、閉部分空間上で時刻1となる連続な時間関数を作る。
`CylinderSubset` は `cylinder-subset` で accepted・終了0・キャッシュ保存失敗0。
閉部分空間の円柱と全体の円柱内の対応する部分空間との互いに逆な連続写像を作る。
`GaugeExtension` は `gauge-extension` で accepted・終了0・キャッシュ保存失敗0。
閉部分空間上で恒等写像から始まる束の自己同型のホモトピーを、全体の束の終点の自己同型へ延長する。
閉被覆上の貼り合わせ・B09 の近傍延長・`CylinderNeighborhood` の時間関数を使う。
`CylinderRestriction`・`FramedClass.Cylinder`・`FramedClass.With.Homotopy` は `framed-homotopy-*` で accepted・終了0・キャッシュ保存失敗0。
前二者は部分空間への制限と円柱への引き戻しを比較し、固定した境界の枠を円柱上へ引き戻す。
後者は `GaugeExtension` を使い、境界の枠のホモトピーに対する被約群の元の不変性を示す。
最新の未検証変更は `CylinderSum`・`CylinderHomotopy`・`TripleHomotopy`。
それぞれ直和と円柱への引き戻しの比較、三つ組のホモトピーの円柱内の部分空間への移動、三つ組のホモトピーに対する被約群の元の不変性を示す。
`TripleClass` は正側を安定化した束のモデルも公開する。
`CylinderSum`・`CylinderHomotopy`・`TripleHomotopy` は `triple-homotopy-*` で accepted・終了0・キャッシュ保存失敗0。
したがって `TripleClass` の全体延長とホモトピーの関係式については被約群の元が保たれる。
直和・合成の関係式の証明はまだ残る。
K07 の剪断写像と符号付き交換の族を、任意の可換環上の `linear_algebra.Commutative.Blocks`・`Rotation` へ移し、K07 の参照先を更新した。
共通 API 自体は `common-Blocks`・`common-Rotation` で accepted・終了0・キャッシュ保存失敗0。
K07 の影響先検査は最終検査に含める。
`FramedSum` の束の同型は `framed-sum-descent`、被約群の加法性は `framed-sum-additive` で accepted・終了0・キャッシュ保存失敗0。
`With.Between` は包含・射影を商へ降ろし、降下した束の直和と直和の降下との同型を作る。
`With.additivity` は束の同型類と自明束の直和の等式から被約群の加法性を導く。
`MapOperations` と `Commutative.Blocks.Interchange` は `shears-MapOperations`・`shears-Interchange` で accepted・終了0・キャッシュ保存失敗0。
共通 API は束写像の加法・定数倍と、同型で結ばれた二つの空間を符号付きで交換する剪断写像の積を作る。
`FramedClass.With.Stabilized`・`Shear`・`BundleSwitch` の符号付き交換は `shears-fixed-*` で accepted・終了0・キャッシュ保存失敗0。
`BundleSwitch` は B09 により境界同型と逆写像を全体の束写像へ延ばし、可逆な剪断写像の積から境界上での符号付き交換を実現する全体の自己同型を作る。
`Negation`・`BundleSwitch.Result.exchange`・`FramedClass.To.Stable` と三つの並べ替えは `reordering-*` ですべて accepted・終了0・キャッシュ保存失敗0。
`FramedClass.To.Stable` は両側へ自明束を加えた後の枠と両立する同型から、元の被約群の元の一致を導く。
`FramedSum` と `Stabilized` は安定化した束のモデル・枠・次元も公開する。
`Commutative.DirectSum.Symmetry`・`CoordinateSum.Symmetry`・`DirectSumMiddleSwap` は直和と座標ブロックの交換・並べ替えを構成する。
`TripleFraming` と `TripleClass.canonicalEquality` は `triple-framing-*` で accepted・終了0・キャッシュ保存失敗0。
前者は負側と補助束の直和の自明化を引数として被約群の元を作り、後者は標準補束を使った場合の既存構成との一致を示す。
`ComplementChoice` は `complement-choice-fixed` で accepted・終了0・キャッシュ保存失敗0。
全体の束の交換自己同型と座標ブロックの交換により、補助束・自明化の選択によらず被約群の元が一致することを示す。
`TripleIsomorphic` は `triple-isomorphic-fixed` で accepted・終了0・キャッシュ保存失敗0。
三つ組の正負の束を境界同型と両立する全体の同型で取り替えた場合の不変性を、共通の補助束へ移して証明する。
`TripleSum` は `triple-sum` で accepted・終了0・キャッシュ保存失敗0。
補助束の直和の射影表示と正負の束の並べ替えにより、三つ組の直和関係が被約群の加法へ移ることを示す。
`TripleComposition` は `triple-composition` で accepted・終了0・キャッシュ保存失敗0。
境界同型に沿う全体の交換自己同型を使い、二つの三つ組の和と合成三つ組に対角三つ組を加えたものを比較する。
これで `TripleClass` は三つ組の四種類の関係式を保つ。
`Group.ToReduced` は `to-reduced` で accepted・終了0・キャッシュ保存失敗0。
関係式を保つ生成元の値を、整数加群の表示の普遍性で被約群への準同型へ拡張する。
`TripleReconstruction`・`GroupRetraction` は `group-retraction-fixed-*` で accepted・終了0・キャッシュ保存失敗0。
標準補束の構成と正規化した射影表示の構成を比較し、三つ組を被約群へ写してから戻すと元に一致することを示す。
`Reconstruction.Normalized.With` は、固定した延長に対する復元等式も公開する。
`TrivialNegative`・`FiberTransport` と `QuotientReconstruction.In` の局所枠からの延長は `quotient-reconstruction-start-*` で accepted・終了0・キャッシュ保存失敗0。
それぞれ負側が自明な三つ組の一般の枠付き束への比較、等しい基点間のファイバーの移送、商上の枠を引き戻して作る指定した延長を構成する。
`QuotientReconstruction.In` の各ファイバーの同型・局所枠との整合性・束の同型は `quotient-reconstruction-near` で accepted・終了0・キャッシュ保存失敗0。
基点上と基点の外の候補から一意な値を定め、元の商上の枠と降下の近傍・外部の枠を比較して連続性を示す。
`FramedTriple`・`QuotientComparison`・`ReducedRetraction`・`Comparison` は `reduced-retraction-*` で accepted・終了0・キャッシュ保存失敗0。
枠付き束の三つ組を被約群へ戻すと元の枠付き束の値になり、商上の束の三つ組の値がその束と基点ランクの自明束との差へ戻ることを示す。
`ReducedRetraction` はランク零の束の差で自明束の次元が一致することを使って逆向きの往復を示し、`Comparison` は両方向の準同型と逆の等式を公開する。
これにより三つ組の群と商の被約群との比較同型は対象検査を完了した。
`Pair.Exact` は `sequence-foundations-Pair-Exact` で accepted・終了0・キャッシュ保存失敗0。
被約群側の忘却・制限の完全性と、忘却の加法性・零性・三つ組上の式を公開する。
`Reduced.Constant`、`Composition`・`Identity` の suspension・反復・負次数の法則、`Group.NormalForm`・`TrivialBoundary` は `sequence-ordered-*` で accepted・終了0・キャッシュ保存失敗0。
定数写像の零性と収縮可能な空間での被約群の零性、負次数の恒等・合成則、任意の群の元を一つの三つ組で表すことを示す。
`TrivialBoundary.With.Contraction` は、自明束の境界の枠を閉部分空間の収縮に沿って動かし、全体へ延びる定数の枠と比較して被約群の零性を示す。
反復の定義が `Identity`・`Composition` の宣言より前に来るよう、上位の宣言順も整えた。
`FramedClass.With.ContractibleKernel` は `contractible-kernel` で accepted・終了0・キャッシュ保存失敗0。
通常の K 群で自明束と一致する枠付き束を安定自明化し、閉部分空間が収縮可能な場合の被約群の零性を示す。
`TrivialBoundary.model`・`With.value` はこの比較で使う束のモデルと値を公開する。
`Group.Forget.Contractible` は `contractible-forget` で accepted・終了0・キャッシュ保存失敗0。
三つ組の表示・正規化・安定自明化・比較同型を使い、収縮可能な閉部分空間に対して忘却写像の核が零であり、忘却が単射であることを示す。
`Exact.Contractible` と `Relative.Cone` は `contractible-comparison-*` で accepted・終了0・キャッシュ保存失敗0。
前者は相対群と全体の基点での被約群との両方向の準同型と逆の等式、後者は K02 の円錐のコンパクト Hausdorff 性・収縮・被約群の零性を構成する。
円錐の収縮を利用するため、`puppe_sequences` の直接依存を追加した。
`Pair.Pointed.Cofiber` と `Equivalence.FromMap` は `compact-cofiber-*` で accepted・終了0・キャッシュ保存失敗0。
前者は閉部分空間の円柱と底面の和から cofiber を構成し、コンパクト Hausdorff 性・底面の埋め込みと閉性・元の商空間への射影を示す。
後者はコンパクト Hausdorff 空間間の連続な基点付き全単射から連続な逆写像を構成する。
`Equivalence.FromMap.Contraction` と `Pair.Pointed.Cofiber.ConeImage` は `cone-image-*` で accepted・終了0・キャッシュ保存失敗0。
円錐を cofiber の閉部分空間として埋め込み、像と元の円錐との同相を構成し、収縮を像へ移す。
最新の未検証変更は `Pair.Pointed.Cofiber.ConeQuotient` と、射影・円錐像・底面の計算補題。
円錐像を潰した商と元の相対商との同相を作り、相対群と cofiber の被約群との比較へ合成する。
固定 snapshot は `work/k03-resume/cone-quotient.source.json`。
`ConeQuotient` は `cone-quotient` で accepted・終了0・キャッシュ保存失敗0。
追加の未検証変更は `FramedClass.With.Pullback` と `Pair.ForgetProjection`。
降下した束の引き戻しの同型と三つ組の正規化から、忘却写像が商への射影による引き戻しに一致することを示す。
`FramedClass.With.Pullback` は `forget-projection-Pair-FramedClass-With-Pullback` で accepted・終了0・キャッシュ保存失敗0。
`ForgetProjection` は module parameter の相対参照で停止し、`On` に正規化 module の import を追加して修正した。
追加の未検証変更は `Pair.Pointed.Cofiber.BaseQuotient`。
底面を潰した商と部分空間の suspension との同相を、円柱と底面からの全射・商の普遍性・両方向の逆の等式で構成する。
`BaseQuotient` の関数型を使う等号除去の構文も修正した。
忘却写像の再検査は等式変形マクロの import 不足で終了1となり、局所 import を補った。
追加の未検証変更は `Pair.Pointed.Exact` で、忘却像のランク零性と基点付き被約群での制限核の完全性を公開する。
修正後の固定 snapshot は `work/k03-resume/cofiber-exact.source.json` で、`Pair.Pointed.Cofiber.BaseQuotient`、`Pair.ForgetProjection`、`Pair.Pointed.Exact` を順に検査中。
追加の未検証変更は cofiber の底面との同相 `BaseImage`、射影との可換図式 `ConeQuotient.Forgetting`・`OriginalDiagram`、底面への制限の完全性 `Restriction`、接続写像と相対群での完全性 `Pointed.Connecting`。
これらの固定 snapshot は `work/k03-resume/connecting.source.json`。
現在の検査終了後、`Pair.Pointed.Cofiber.ConeQuotient.Forgetting`、`Pair.Pointed.Cofiber.BaseImage`、`Pair.Pointed.Cofiber.Restriction`、`Pair.Pointed.Cofiber.OriginalDiagram`、`Pair.Pointed.Connecting` を順に検査する。

検査には `--memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 --diagnostics compact` を指定する。
固定 snapshot、JSON 報告、実行シェルの終了コードを `work/k03-resume` に保存する。
古い `framed-outside` と `framed-outside-diagnostic` は終了130で中断した検査であり、後続の固定 snapshot の検査結果と区別する。

汎用の有限列挙・基点付き suspension・Hausdorff 分離を共通層へ移し、局所検査の依存閉包を縮小した。
移動元を含む K02・単体・胞体座標・近似理論・clutching の影響先は最終検査に含める。

残る主な要件は、負次数までの長完全列、Mayer–Vietoris、外積と自然性、束の円板球面対への適用と具体例。
公開登録・ロードマップ・下流リンクと、package・依存閉包・影響先・workspace 全体の最終検証も未完了。

時間反転の未検証変更は `Suspension.Reversal` で、反転写像・連続性・二回反転の等式と基点付き同相を構成する。
`Pointed.Rotation.Inner`・`Outer` は二段の cofiber から全体空間の suspension への連続な族を構成する。
その時間座標は `multiply (advance h t) (reverse s)` で、内外の円錐の潰される部分で値が基点になることを示して商へ降ろす。
現在の固定 snapshot は `work/k03-resume/rotation.source.json`。
時間両端を suspension の包含・反転と照合する未検証変更を `Pointed.Rotation.Endpoints` に追加した。
始点は二段目の底面の商と底面の同相の suspension から、終点は二段目の円錐像を潰す商・一段目の底面の商・包含の suspension・時間反転から構成する。
`Endpoints.homotopy` と `equation` は両端の写像のホモトピーと被約群への引き戻しの一致を公開する。
固定 snapshot は `work/k03-resume/rotation-endpoints.source.json`。
対象検査は既存の `cofiber-exact` の終了後に行う。

`Suspension.Reversal.Naturality` は suspension の写像と時間反転の可換性を示す未検証変更。
`Pointed.LeftExact` は二段目の接続写像と底面の商の比較から、接続写像の核をその合成写像の像として表す未検証変更。
通常の suspension の包含の像との照合には `Rotation.Endpoints.equation` と反転の自然性を使う。
比較写像と接続写像の零元の保存も追加した。
固定 snapshot は `work/k03-resume/left-exact-natural.source.json`。

`BaseQuotient` の比較では、明示的な逆写像の連続性を円柱から直接示し、一般の全単射から逆写像を再度選ぶ構成を省いた。
旧 `cofiber-exact` snapshot の長い検査は、この変更を保存後に中断として記録し、新しい snapshot で再開する。
追加の未検証変更 `BaseQuotient.Forgetting` と `Connecting.pullbackEquation` は、接続写像を cofiber からの商写像による引き戻しとして表す。
次の固定 snapshot は `work/k03-resume/direct-inverse.source.json`。
旧 `cofiber-exact-Pair-Pointed-Cofiber-BaseQuotient` は終了130・`interrupted`・キャッシュ保存失敗0で中断した。
同じ batch の後続二対象は未実行。

`Rotation.Endpoints.Pullbacks` は変形の引き戻しの式から、二段目の接続写像と通常の suspension の包含による写像を時間反転を介して比較する未検証変更。
`LeftExact.Suspension` は反転の可逆性と底面の同相を使って、suspension の包含の像と接続写像の核の一致を示す。
`Pointed.FiveTerm` は基点が閉部分空間にある対について、負一次から被約零次までの五項の群・加法的写像・中間三箇所の完全性を公開する。
これらも未検証で、固定 snapshot は `work/k03-resume/five-term-public.source.json`。
現在の `direct-inverse` 検査には、この後に追加した証明を含めていない。

`Pair.ForgetProjection` と `Pointed.Exact` は `direct-inverse-*` で accepted・終了0・キャッシュ保存失敗0。
現在は同じ batch の `BaseQuotient.Raw`、`Backward`、比較全体の順に検査を進めている。
追加の未検証変更 `Pointed.SuspendedPair` は、閉部分空間の suspension を全体の suspension に閉埋め込みし、その像との基点付き同相を構成する。
`ClosedPointedPair`・`PointedPair`・`iteratePair` は suspension を繰り返すための対のデータと反復を公開する。
固定 snapshot は `work/k03-resume/suspended-pair.source.json`。
対の商と商の suspension の同相、および反復した五項の列との照合は次に実装する。

`SuspendedPair.Quotient` は対の商と商空間の suspension の同相を構成する未検証変更。
射影の suspension を商へ降ろし、商の関係式から単射性を示し、元の商への射影の全射性から全射性を示す。
`QuotientSurjective` は基点が部分空間に含まれる対で、付加した基点も元の空間からの射影で表せることを示す。
`Equivalence.Compose` と `PairIteration` は比較同相を反復し、反復した対の相対群と元の商の負次数群との両方向の加法的写像を公開する。
固定 snapshot は `work/k03-resume/iterated-quotient.source.json` で、これらは未検証。

`PairIteration.wholeComparison`・`subsetComparison` は、全体空間と部分空間についても反復 suspension との基点付き同相を構成する未検証変更。
部分空間側は suspension の像との同相を逆向きに使い、前段の比較の suspension と合成する。
`WholeGroups`・`SubsetGroups` と相対群の `Groups` は両方向の写像・加法性・零元の保存・逆の等式を公開する。
固定 snapshot は `work/k03-resume/pair-iteration.source.json`。

`PairIteration.inclusionNaturality`・`projectionNaturality` は、反復した対の包含・商への射影と、元の写像の反復 suspension との可換性を示す未検証変更。
包含の帰納段階では suspension の像との同相の逆写像を使い、射影の帰納段階では `PointedPair.suspendedProjectionEquation` を使う。
固定 snapshot は `work/k03-resume/iteration-coherence.source.json`。

`InclusionPullback`・`ProjectionPullback`・`SuspendedInclusion` は、包含・射影の可換図式を K 群の引き戻しの等式へ移す未検証変更。
`PairIteration.Sequence` は各次数の五項の列を比較同型で移し、加法性・零元の保存・中間三箇所の完全性を構成する。
写像と通常の負次数の引き戻しとの一致、隣り合う次数の制限写像の一致も構成したが未検証。
`BaseQuotient.Raw` の長い検査を受け、公開写像の戻り値型を一定の商空間にそろえ、一意選択の証拠を内部の `chosen` に分けた。
その module の宣言を K 群の import より前へ移し、位相的な構成に不要な依存を除いた。
旧 `direct-inverse` batch の `Raw` の検査は、この変更を保存した後に中断として記録する。
次の固定 snapshot は `work/k03-resume/constant-raw.source.json`。
旧 `direct-inverse-Pair-Pointed-Cofiber-BaseQuotient-Raw` は終了130・`interrupted`・キャッシュ保存失敗0で中断した。
同じ batch の `ForgetProjection`・`Pointed.Exact` は accepted・終了0・キャッシュ保存失敗0で、後続の `Backward`・比較全体は未実行。

`constant-raw` の通常検査は宣言ごとの時間計測を付けて再開する。
処理系の既存の `REF_TYPE_PROFILE_DECLARATIONS` と `REF_TYPE_PROFILE_PHASES` を使い、固定 snapshot `constant-raw.source.json` と共有キャッシュを維持する。
