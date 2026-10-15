# 非負鎖複体と二重複体

`double_complexes` は非負鎖複体、その整数次数への零拡張、第一象限の二重複体と total を構成する。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`NonnegativeChain.Over` は鎖写像、ホモトピー、ホモロジー、短完全列と長完全列の自然性を扱う。
`ZeroExtension` は `DegreeZeroHomology`・`PositiveHomology`・`NegativeHomology` で元のホモロジーとの同型と負次数の消滅を公開する。
`Isomorphism.With.At` は鎖同型から非負次数のホモロジー同型を構成する。
`ShortExact.Morphism.Straighten` は比較写像をホモトピーで補正し、増大写像を保った可換図式を構成する。

`DoubleComplex.Over.TensorMapping.With` は両因子の鎖写像からテンソル二重複体と total の鎖写像を作る。
`Total` の微分は水平微分と第一次数の符号を掛けた垂直微分の和であり、`Coordinates.StepAt` はその各成分の公式を公開する。
`Coordinates.Degree` の座標は零元を検出し、直和への包含上の公式と線形性を持つ。
`Concentrated`・`ConcentratedFirst` は片方の正次数の項が零の場合に total を零次の列・行と鎖同型にする。

`DoubleComplex.Over.Collapse.On.Exact.exact` は、各行の増大写像の核の完全性と正次数の完全性から total 比較写像の核の完全性を証明する。
有限対角の最大の第一次数の成分を境界で消し、`Descent.finiteDescent` の有限帰納法で境界元を構成する。
境界元も比較写像の核に入ることを保持し、`On.Surjection.onto` と `NonnegativeChain.Over.Map.SurjectiveQuasi` によってホモロジー同型を得る。
`CollapseFirst` は符号を補正した `SignedTranspose` とその total の鎖同型を通じ、水平の完全性にも同じ結果を適用する。

`DoubleComplex.Over.TensorSwap` は符号 \((-1)^{pq}\) を持つ交換鎖同型と、二回交換したときの恒等則を公開する。

`DoubleComplex.Over.TensorSplitSequence.With.Split` は、各次数で分裂する鎖複体の短完全列を、固定したもう一つの複体とのテンソル total の短完全列へ移す。
分裂が鎖写像であることは要求せず、各次数の線形な左逆からテンソル積と対角直和の完全性を構成する。

テンソル比較と射影分解への適用は [resolutions](../resolutions/README.md)、整数次数のテンソル鎖複体は [tensor_chains](../tensor_chains/README.md) にある。

```sh
cargo run -p cli -- libs/algebra/homological/double_complexes --module double_complexes
```
