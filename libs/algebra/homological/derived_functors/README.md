# 導来関手

可換環上の Ext・Tor、分解からの独立性、自然性、普遍係数を扱う。

| module | 内容 |
| --- | --- |
| `Ext.Over.Of` / `Tor.Over.Of` | 指定した射影分解による各次数の加群 |
| `Independence` / `DegreeZero` | 分解変更同型、零次の Hom・テンソルとの同型 |
| `IntegerCyclicResolution` | 整数巡回加群の分解と Ext・Tor の計算 |
| `Tor.Over.Balance.With.At` | 両変数のどちらを分解しても同じ Tor を得る比較同型 |
| `Balance.Naturality.With.At` / `Balance.With.Swap.At` | 両変数の自然性、二回交換の恒等則 |
| `ShortExactFirst.With.On.Balance.With.At` | 変数交換と長完全列の接続写像の整合性 |
| `Tor.Over.ProjectiveSecond` | 射影係数との因子交換、正次数の消滅 |
| `Ext.Over.Extension.With` | Ext¹ と第1シジジーからの準同型の商 |
| `OfExtension.With` / `RepresentationClass` / `Compare` | 拡大の類、全類の表示、拡大同型との対応 |
| `UniversalCoefficient.Over.Projective.At` | 境界・サイクルの射影性から得る Ext¹・Tor₁ の短完全列 |
| `Selected` / `ChoiceIndependence` | 分裂の選択と座標変換 |
| `ExactNaturality` / `ExactIdentity` / `ExactComposition` | 短完全列の端の写像と恒等・合成 |

Tor の比較は二重分解の total を介し、`onComparison` が実際の誘導写像との一致を示す。
消滅定理の利用例は [Cyclic.ProjectiveCoefficient](../concrete_complexes/src/Cyclic/ProjectiveCoefficient.ref) にある。
