# 導来関手

Ext・Tor、分解からの独立性と自然性、巡回加群の分解、普遍係数を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`Ext.Over` と `Tor.Over` は可換環上の加群の導来関手を扱う。
`IntegerCyclicResolution` は整数の巡回加群の射影分解と Ext・Tor の計算を、`UniversalCoefficient` は指定した複体の普遍係数写像を提供する。

`derived_functors.Ext.Over.Of` と `derived_functors.Tor.Over.Of` は指定した射影分解から得た加群を各次数に返す。
`Independence` は同じ加群の別の分解との同型を、`DegreeZero` は Hom とテンソル積との零次の同型を提供する。

`derived_functors.Ext.Over.Extension.With` は指定した射影分解の Ext¹ を、第1シジジーからの準同型の商と同型にする。
`OfExtension.With.extClass` は短完全拡大に対応する Ext¹ の類を返す。
`RepresentationClass` は押し出しで代表となる拡大を作り、`represented` は全類の代表の存在を示す。
`Compare.correspondence` は類の一致と、両端の加群を固定する拡大の同型との対応を証明する。
`OfExtension.With.Split.extZero` は切断を持つ拡大が零類になることを示す。

検査方法と関連パッケージは [ライブラリ一覧](../README.md) を参照。
