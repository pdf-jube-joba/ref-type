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

`Pair.Mapping.Augmented.Negative` に一般の対の接続・忘却・制限の自然性を書いた（未検証）。
残る構成は Mayer–Vietoris の残る位置での完全性、外積と自然性。
検査完了後、公開登録・ロードマップ・下流リンクを整備する。
K02・K07・単体/胞体・近似理論・B09 の影響先と workspace 全体を最終検証に含める。

`qualified-PairIteration` は部分空間の恒等比較の構成を拒否した（型不一致）。
恒等比較を任意の `CompactPointed` 上で一度構成し、部分空間へ実体化する形に整理した。
修正 snapshot は `iteration-identities.source.json`、対象は `PairIteration --module-only`、診断は `detailed` を使う。
`mayer-positive.source.json` では差の写像と正の負次数側の和の位置の完全性まで構文解析を通過した。
この追加、一般の対の自然性、群の補助計算はいずれも未検証。
Mayer–Vietoris の交叉部分の完全性も証明コードを追加し、構文解析を通過した（未検証、`mayer-intersection.source.json`）。
次数0の和の位置の完全性には、閉被覆上の束の貼り合わせを構成する。
`ClosedCover.Patching` に交叉上の同型から有限次元の交差写像を作り、Tietze で全体へ延長する入口を書いた。
延長写像による剪断・射影の貼り合わせ、次数0の完全性、外積は構成中。

恒等比較の整理後は `InclusionStep.pointwise` まで進み、`WholeStep` の移送された写像と直接 suspension した写像との不一致を検出した。
`WholeStep.result` を定義上同じ型の `Suspended.result` から直接取るよう整理した（未検証）。
再検査 snapshot は `iteration-direct-whole.source.json`。
`PairIteration.WholeStep`・`SubsetStep`・`InclusionStep`・`ProjectionStep` をそれぞれ `--module-only` で先に保存し、その後 `PairIteration` と `PairIteration.Sequence` を検査する。
`Patching` の剪断の構成と射影との交叉上の可換式も追加したが、型検査は未完了。

`Patching.On.With.Using.Local` では、共通の束の引き戻しと自明束の直和を比較し、両側の射影を連続な束写像にした。
`Glued` は交叉上の共役の式に沿って冪等写像を閉被覆で貼り、`Glued.Image` はその像束と K01 の射影表示の存在を構成する。
ここまでは `patching-image.source.json` で構文解析を通過したが、型検査は未完了。
像束と元の両側の束との制限同型、および K 群の次数0の完全性への接続を続ける。

`direct-whole-*` の `QuotientStep`・`WholeStep`・`SubsetStep`・`InclusionStep`・`ProjectionStep`・`PairIteration` はすべて accepted・終了0・保存失敗0。
続く `PairIteration.Sequence` を同じ snapshot で検査中。
`Patching.ImagePair` は矩形の交差写像から射影像の束同型を構成する。
`Glued.Image.Left`・`Right` には像束の両側の制限同型と K 群の制限式を追加した（`patching-restrictions.source.json`、構文解析のみ完了）。
安定同型判定を通して仮想束の貼り合わせへ移す証明を続ける。

`PairIteration.Sequence` は制限写像の値域の照合で不一致を検出した。
列の端の群に元の対を明示して `iteration-base-pair.source.json` に固定した（未検証）。
先に `PairIteration.Groups`・`WholeGroups`・`SubsetGroups` をそれぞれ `--module-only` で保存し、その後 `Sequence` を検査する。
通常の K 群には `K0.NormalForm` として、任意の元を束の表示と有限次元自明束との差へ直す構成も追加した（未検証）。

`Patching.Ordinary.existence` は、交叉上で一致する通常の K 群の二つの元に、大域的な元と両側の制限式を構成する。
`K0.NormalForm`・安定同型判定で正側の束をそろえ、射影の貼り合わせ後に共通の自明束を差し引く。
自明束の引き戻し、K 群の加法・逆元・差の引き戻しの式も追加した。
`ordinary-patching.source.json` で構文解析を通過したが、型検査は未完了。
既存の Mayer–Vietoris の次数0の端への比較と、外積の構成を続ける。

`Reduced.Multiplication` と `Pullback.Multiplication` に被約群の積とその自然性を書いた。
`Smash` はコンパクトな積空間と閉じた wedge の相対商を構成する。
`Smash.Split.QuotientEquivalence` は wedge の一方の軸を潰した商と他方の空間の同相を構成する。
`WedgeDecomposition` では各負次数の類を二軸からの引き戻しの和に分解し、積から wedge への制限の全射性を示す。
`Smash.External` は積上の被約 K 類の積を相対群へ一意に持ち上げ、双加法性と零の式を構成する。
`ConstantMap.Negative` は基点への定数写像が各負次数で零になることを示す。
いずれも `smash-external.source.json` で構文解析を通過したが、型検査は未完了。
外積の自然性、元の二つの対の積の商との比較、suspension との比較を続ける。

再開記録（K03、2026-10-27）: 外積の零次数構成を commit `e950e890` に保存した。`PairIteration.Sequence` の再検査は終了コード1、キャッシュ保存失敗0、書込失敗0で、最後の制限写像の戻り型を拒否した。第五項を完全修飾した負次数群へ直接指定する修正を加えた。次は `work/k03-resume/iteration-canonical-fifth.source.json` の同 module を検査し、最新全体の検証とは区別する。外積・貼合せの追加分は構文解析のみで型検査は未完了。

再開記録（K03、続き）: `Smash.Mapping.External.naturality`、`ClosedCover.MayerVietorisZero.exactPieces`、閉対の積と smash の商比較、および零次数外積のコードを追加した。いずれも型検査は未完了で、`work/k03-resume/relative-external.source.json` が構文解析用スナップショット。進行中の型検査は `canonical-fifth-Sequence.{log,json,exit}` を回収し、同じ範囲を重複起動しない。商比較の単射・全射は商の同値関係と代表元から構成する。

再開記録（K03、負次数外積）: `CommonQuotient` は既存の商写像の descent を使い、同じファイバーを持つ二つのコンパクト商を比較する。`Smash.Suspension` は円柱上でその同値関係を証明し、`Symmetry`・左右の反復から `Smash.Graded` と `Pair.Product.Negative` を構成した。結果の次数は `secondDegree + firstDegree`。双加法性と零元の式を含む追加分は型検査未完了。構文解析用の最新 snapshot は `graded-external.source.json`。継続中の対象検査は `canonical-fifth-Sequence` を先に回収する。負次数外積の自然性、閉被覆の写像に対する自然性、対象・依存・影響先・全 workspace の最終検証、公開情報の整備が残る。

再開記録（K03、外積の自然性）: 円柱上の式から `Smash.Mapping.SuspensionNaturality` と対称性・右 suspension の自然性を追加し、左右の反復比較を帰納した。反復次数の組替えは `IterationAddition` の帰納的同相へ変更し、`Smash.Mapping.GradedNaturality` で負次数外積を通常の引き戻しと比較するコードを追加した。これらは型検査未完了。`canonical-fifth-Sequence` は第五項と全写像の式を通過し、検査後の直列化・保存処理中なので、終了コード・JSON を回収してから成功を確定する。

検証結果（K03）: `canonical-fifth-Sequence` は `accepted`・終了0・保存失敗0・書込失敗0を確認した。固定 snapshot `iteration-canonical-fifth.source.json` に対する `PairIteration.Sequence` 全体の検査で、316 modules / 4,317 steps を検査した。最新の自然性・外積・貼合せ全体の成功とは区別する。次の検査は `graded-natural.source.json` を固定し、`IterationAddition`、`Square`、`Absolute`、`Pair.Augmented`、`PairMapping`、`Smash`、`Pair.ClosedCover` の順に進める。共有キャッシュは `libs/refcache`、メモリ14336 MiB・キャッシュ上限16384 MiB、各 `graded-stage-*.{log,json,exit}` を回収し、拒否ならその範囲を修正する。

再開記録（K03、対象検査の修正）: `graded-stage-IterationAddition` は終了1・rejected・保存失敗0・書込失敗0。親への直接の値参照が module のパスとして解釈されるため、`IterationAddition.Mapping.At` と smash 比較の同形参照を完全修飾へ直した。次は `graded-qualified.source.json` の同じ検査順を `qualified-stage-*` へ記録する。閉対の積の `Pullback` と零次数・負次数外積の自然性も追加したが、こちらは `pair-external-natural.source.json` の構文解析のみで、修正後の最終全体検証は未完了。

再開記録（K03、構成の接続）: 閉被覆の写像について `ClosedCover.Mapping.Negative` が切除・制限・差・境界の自然性を構成した。`BundleDisk.With.OriginalUnit` は表現から作った円板と元の束の単位円板との同相、球面条件の一致を構成する。`Pair.Mapping.Group` は商の被約群の引き戻しを比較同型で三つ組の群へ運び、加法・零元と比較の自然性を示す。これらは型検査未完了。最新ソース snapshot は `group-natural.source.json`（構文解析中）。修正後の `qualified-stage-IterationAddition` と `qualified-stage-Square` は accepted・終了0・保存失敗0・書込失敗0。`qualified-stage-Absolute` 以降の逐次検査が session 97607 で進行中のため先に回収する。

再開記録（K03、公開名の修正）: `qualified-stage-Absolute` は終了1・rejected・保存失敗0・書込失敗0で、`Absolute.Mapping.Naturality` が非公開の `Source.Ordinary` を参照していた。公開 `KTheory.On.K0` を `SourceOrdinary` として明示 import する修正を加えた。現在までの追加全体は `group-natural.source.json` で構文解析終了0。次は修正と最新の数学ソースを `implementation-complete.source.json` に固定し、`Absolute`、`Pair.Augmented`、`PairMapping`、`Smash`、`Pair.ClosedCover`、`Pair.Product`、`BundleDisk`、`Examples` の順に `complete-stage-*` を検査する。これらが通った後に package の依存閉包・全 workspace の最終検査へ進む。

再開記録（K03、負次数比較の式）: 差分レビューで `Pair.Product.Pullback.Negative` の自然性に、同相から運んだ負次数の準同型と標準引き戻しの間の `forwardEquality` を明示する補足を加えた。進行中の `complete-stage-*` は修正前の固定入力であり、この一ファイルは次の `product-comparison.source.json` 以降で検査する。

再開記録（K03、通常の群の端）: `complete-stage-Absolute` は accepted・終了0・保存失敗0・書込失敗0（447 modules検査、957再利用）。`complete-stage-Pair-Augmented` は終了1・rejected・保存失敗0・書込失敗0で、`OrdinaryEnd.forgetFormula` の合同則へ被約群を定義域とする関数として通常の環準同型を渡せなかった。`WholeInclusion.map`・`SubsetInclusion.map` を被約群の元に適用するラムダへ明示化した。次は `ordinary-restriction.source.json` を固定し、`Pair.Augmented` から同じ順で検査する。この入力は前回の負次数外積の比較式の修正も含む。
