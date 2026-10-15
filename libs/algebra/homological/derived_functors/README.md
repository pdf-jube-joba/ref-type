# 導来関手

Ext・Tor、分解からの独立性と自然性、巡回加群の分解、普遍係数を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`Ext.Over` と `Tor.Over` は可換環上の加群の導来関手を扱う。
`IntegerCyclicResolution` は整数の巡回加群の射影分解と Ext・Tor の計算を、`UniversalCoefficient` は指定した複体の普遍係数写像を提供する。

`UniversalCoefficient.Over.Projective.At` は、境界とサイクルの射影性を `Hypotheses` にまとめ、Ext¹ と Tor₁ の普遍係数短完全列の存在を証明する。
`Selected` はサイクルへの二つのリトラクションを選んだ構成を公開し、`ChoiceIndependence` は短完全列の一致と、選んだ分裂の間の座標変換を返す。
`ExactNaturality.Kernel` と `Cokernel` は短完全列の可換な一方の正方形からもう一方の端の写像を一意に構成し、`ExactIdentity` と `ExactComposition` は恒等・合成との整合性を証明する。
`LengthOneMapping` は短完全列の可換図式を長さ1の分解の鎖写像へ移す。

`derived_functors.Ext.Over.Of` と `derived_functors.Tor.Over.Of` は指定した射影分解から得た加群を各次数に返す。
`Independence` は同じ加群の別の分解との同型を、`DegreeZero` は Hom とテンソル積との零次の同型を提供する。

`Tor.Over.Balance.With.At.isomorphism` は、両変数のどちらを射影分解しても得られる Tor が一致することを、二重分解の total を介して証明する。
`left`・`right` は各比較鎖写像の実際のホモロジー写像であり、`onComparison` は同型がそれらを結ぶことを示す。
`Balance.Naturality.With.At.naturality` は分解変更と両変数の係数写像についてこの同型の可換性を証明する。
`Balance.With.Swap.At.leftInverse`・`rightInverse` は変数交換を二回行うと恒等写像になることを示す。
`Tor.Over.Second.PositiveAgreement.agrees` は、零拡張による一様な次数表示と従来の正次数表示の係数写像が一致することを証明する。
`ShortExactFirst.With.On.Balance.With.At.connectingNaturality` は、Horseshoe 分解から得た第一変数の長完全列と、変数交換後の第二変数の長完全列の接続写像を結ぶ。
次数ごとに分裂する分解の短完全列を二重テンソル total の短完全列へ移し、両側の比較鎖写像について接続写像の自然性を適用する。

`Tor.Over.ProjectiveSecond` は、指定した分解のテンソル複体と、係数加群を左因子に置いた複体の間に因子交換の鎖写像を構成する。
`Degree.forward`・`backward` は各項の交換とその逆であり、`Step` は両方向で微分との可換性を証明する。
`Positive.vanishing` は第二変数の射影性と第一変数の射影分解を命題内の前提として受け取り、すべての正次数の Tor の消滅を証明する。
[利用例](../../../../libs/algebra/homological/concrete_complexes/src/Cyclic/ProjectiveCoefficient.ref)は、第一変数を \(\mathbb Z/2\)、第二変数を \(\mathbb Z\) としてこの定理を適用する。

`derived_functors.Ext.Over.Extension.With` は指定した射影分解の Ext¹ を、第1シジジーからの準同型の商と同型にする。
`OfExtension.With.extClass` は短完全拡大に対応する Ext¹ の類を返す。
`RepresentationClass` は押し出しで代表となる拡大を作り、`represented` は全類の代表の存在を示す。
`Compare.correspondence` は類の一致と、両端の加群を固定する拡大の同型との対応を証明する。
`OfExtension.With.Split.extZero` は切断を持つ拡大が零類になることを示す。

検査方法と関連パッケージは [ライブラリ一覧](../../../README.md) を参照。
