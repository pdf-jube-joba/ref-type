# 相対 K 群（K03）

B09 統合済み main `bd8fd86d5368968ff22e06f81beb5469bc348623` から、`math/k03-relative-k` / [Draft PR #50](https://github.com/pdf-jube-joba/ref-type/pull/50) で実装中。
[計画](../../../_plans/math/k03-relative-k.md)は未完成。

## 現在の構成

入口は `relative_k_theory.Relative`。
`Pair.Quotient` は一点を付加してから閉部分空間とともに潰すため、空の部分空間も同じ定義で扱う。
その被約 K 群と反復 suspension による負次数群、対の写像による引き戻しを構成した。
`PullbackIdentity`・`PullbackComposition`・`HomotopyInvariance` が基本的な関手性を与える。

`Pair.Triple` は射影表示による二つの束と、閉部分空間上の同型を持つ。
`Pair.Group` は全体に延長する同型・直和・合成・ホモトピーの関係式による群で、対角三つ組の零性と逆元を証明した。
`Pair.SumConstruction` は任意の二つの三つ組の直和を、比較同型とともに構成する。

`Descent.descend` は閉部分空間上で自明化された束を商空間へ降ろす。
`Descent.With.Construction` は商上の束・基点でのランク・元の束との引き戻し比較・境界上の整合式を提供する。
降下のファイバーは基点での座標と商のファイバー上の整合するベクトルから作り、B09 の近傍延長と基点外の同相で局所自明化する。
共通の位相と線形代数の補題は `Coproduct.Properties`・`Collapse.Closed`・`Collapse.Outside`・`Commutative.DependentProduct`・`Atlas.Using.Overlap` に置いた。

## 検証と再開

共有キャッシュは `libs/refcache`。
以下の対象検査はすべて accepted・終了0・キャッシュ保存失敗0で、報告・ログ・終了コードは `work/k03-resume` に保存した。

| 範囲 | 報告の接頭辞 |
| --- | --- |
| 三つ組の群、引き戻し、ホモトピー不変性 | `group-fixed` |
| 一点付加商の基点外の同相、降下のファイバーと枠 | `outside-batch-*` |
| 座標の読み書きの連続性 | `coordinates-batch-Descent` |
| 座標変換の共通 API、降下の開被覆 | `cover-batch-*` |
| 降下した束と元の束の比較同型 | `descent-comparison-fixed` |
| 降下の存在、ランク、境界上の整合式 | `descent-public-fixed` |
| 三つ組の直和の存在と比較 | `triple-sums` |
| 標準ライブラリへ移した有限列挙 API | `common-ListIndex` |
| 共通化した Hausdorff 性の補題 | `common-Separation` |
| 共通化した基点付き suspension と写像 | `common-pointed-fixed` |
| 境界上一定の行列の商への降下 | `matrix-descent-fixed` |
| 境界枠と両立する束写像の商への降下 | `framed-public` |
| 降下の同型、近傍の選択独立性、被約群の元 | `framed-choices-public` |
| 補束による三つ組の正規化と降下への接続 | `triple-normalize` |
| 境界の自明化と両立する写像のファイバー上の構成 | `framed-maps` |

`Pair.Normalize` は補射影から補束を作り、対角三つ組を加えて群の元を保ち、負側を自明束にした後 `Descent` へ渡す。
`Pair.FramedMaps` は境界の自明化と定数行列に両立する束写像を、商上のアンカーと各ベクトルへ点ごとに適用する。
その束写像としての連続性も `framed-public` で検査済み。
共通 API `bundle_operations.Operations.Over.LocalMatrices` は `local-matrices-fixed` で accepted・終了0・キャッシュ保存失敗0。
異なる次元の二つの枠の間の連続な行列表示から、束写像の連続性を導く。
未検証変更は `Pair.FramedMaps.With.Between` の連続性の証明。
`Outside` は基点外の二つの枠による連続性、`Near` は共通のコンパクト近傍における行列の Tietze 延長、`Quotient.Matrices` は境界上一定の行列の商への降下を構成する。
`framed-outside` は一つの module の検査が長引いたため中断し、終了130を確認した。
同じ検査の成功は未確認で、診断ログ付きで原因を確認する。
次は新しい snapshot を保存し、共有キャッシュで `relative_k_theory.Relative.Pair.FramedMaps.With.Between` を検査する。
`Pair.FramedIsomorphisms` は逆写像の境界整合性と降下上の逆法則、`Pair.FramedChoices` は同じ境界枠での近傍の選択によらない同型を追加したが未検証。
`FramedChoices.With.Value` は基点ランク零の差の元を構成するが未検証。
`Pair.Excision` は開集合を閉部分空間の内部から取り除いた対と元の対の商の間の同相を構成するが未検証。
共通の `Collapse.Mapping.injective` と `Coproduct.Properties.rightInjective` を併せて追加した。
`Relative.Equivalence` は基点付き同相の引き戻しと suspension の反復による負次数群の同型を構成し、`Pair.Excision` へ接続したが未検証。
`Pair.Group.Forget` は三つ組から正側と負側の差を取る準同型を構成したが未検証。
診断付きの `framed-outside-diagnostic` は依存整理後の入力へ切り替えるため中断し、終了130・outcome interrupted・キャッシュ保存失敗0を確認した。
K03 の追加部分に到達する前の中断で、成功扱いにはしていない。
worker 内のログは共有キャッシュ直下の `.check-<PID>-0/stderr` と `events.jsonl` にあり、完了後には監督プロセスが外側のログへ回収する。
`events.jsonl` の Planned 行は大きいため、必要なイベントだけ JSON として読む。
局所検査の依存閉包を小さくするため、基点付き suspension を `algebraic_topology.Suspension.Pointed` へ共通化し、K02 と K03 から参照するようにした。
有限列挙の汎用 API `ListIndex` を単体ホモロジー package から `std.Data.ListIndex` へ移し、束演算のホモロジー依存を外した。
これらの共通化も未検証で、最終的に K02・単体・胞体座標を含む影響先と workspace 全体を検査する。
積空間の Hausdorff 性の汎用補題も `topological_constructions.Separation` へ移し、B09 と K03 から近似理論への依存を外した。
読み込む依存閉包は旧 snapshot の6,470 modules から2,683 modules に減った。
この共通化も未検証で、近似理論と clutching の影響先を最終検査に含める。
`common-Pointed` はマクロ参照不足で rejected・終了1になったが、修正した `common-pointed-fixed` は accepted・終了0・キャッシュ保存失敗0。
`framed-outside-lean` は104秒で K03 の行列降下に到達し、`constantContinuous` の参照先誤りで rejected・終了1になった。
該当3箇所を `topology.Maps.constantContinuous` へ直した。
`Pair.Restriction` と `Group.Forget.ToSubset` に制限写像と生成元での零性を追加したが未検証。
`matrix-descent-fixed` は accepted・終了0・キャッシュ保存失敗0。
束写像の対象検査で、他 module の内部 import alias を公開名として参照していた箇所が見つかり、直接 import と公開された型・存在定理へ修正している。
`framed-public` は accepted・終了0・キャッシュ保存失敗0。
`FramedIsomorphisms` と `FramedChoices` についても、内部 import alias に依存しない参照へ修正した。
`framed-choices-public` は accepted・終了0・キャッシュ保存失敗0。
忘却・制限・切除・基点付き同値の各 module でも内部 import alias の参照を修正したが、これらは未検証。
次は最新 snapshot を作り、`Relative.Pair.Group.Forget`・`Relative.Equivalence`・`Relative.Pair.Excision` を順に検査する。
次は共有 suspension と列挙 API、基点外の写像、行列の降下、基点近傍の写像、選択独立性、忘却準同型、切除の順に対象検査を行う。
検査には `--memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 --diagnostics compact` を指定し、JSON 報告と実行シェルの終了コードも保存する。

残る主な要件は、選択に依存しない三つ組の群と商空間の被約群の比較、完全列・切除・Mayer–Vietoris・外積と自然性、円板球面対への適用と具体例。
package・依存閉包・影響先・workspace 全体の最終検証と公開登録の仕上げも未実施。
