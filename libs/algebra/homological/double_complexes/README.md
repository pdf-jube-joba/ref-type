# 非負鎖複体と二重複体

| module | 内容 |
| --- | --- |
| `NonnegativeChain.Over` | 非負鎖複体、写像・ホモトピー、ホモロジー、短完全列と接続写像 |
| `ZeroExtension` | 整数次数への零拡張とホモロジー同型 |
| `Homotopy.ZeroExtension` / `Equivalence.ZeroExtension` | 鎖ホモトピーと同値の零拡張、誘導写像のホモロジー同型 |
| `SplitInjection.On` | 次数ごとの線形な左逆を持つ包含の商複体、短完全列と相対長完全列 |
| `ShortExact.Morphism.Straighten` | 比較写像をホモトピーで補正する可換図式 |
| `DoubleComplex.Over.Total` | 第一象限の有限対角直和と微分 \(d_h+(-1)^p d_v\) |
| `Coordinates.StepAt` / `Degree` | 微分の成分公式、成分による零の判定 |
| `Concentrated` / `ConcentratedFirst` | 正次数の項が零のときの行・列との鎖同型 |
| `Collapse.On.Exact` / `CollapseFirst` | 増大写像の核と正次数の完全性から得る total 比較同型 |
| `TensorMapping.With` / `TensorSwap` | 両因子の写像、符号 \((-1)^{pq}\) の交換鎖同型 |
| `TensorSplitSequence.With.Split` | 次数ごとに分裂する短完全列のテンソル total |

`Collapse` は対角の最大の第一次数を境界で消す有限帰納法を使う。
`SignedTranspose` で符号を補正し、水平の完全性にも適用する。
[分解への適用](../resolutions/README.md) と [整数次数の total](../tensor_chains/README.md) を参照。
