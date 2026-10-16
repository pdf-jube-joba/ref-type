# 射影分解

| module | 内容 |
| --- | --- |
| `Resolution.Over` | 非負次数の射影分解、比較写像とホモトピーによる一意性 |
| `Resolution.Over.ShortExact.Sequence` | 増大写像と整合する分解の短完全列 |
| `Morphism.With.existence` | 係数の可換図式の持ち上げ |
| `ResolutionTensor.Over.Of.With` | 射影加群とのテンソルによる分解 |
| `ResolutionTensor.Over.Double.With` | 二つの分解のテンソル total、片側との比較 `standardLeft` / `standardRight` |
| `With.LeftQuasi` / `RightQuasi` | 行・列の完全性によるホモロジー同型と誘導写像との一致 |
| `Naturality.With.Left` / `Right` | 分解写像・係数写像による比較の自然性 |
| `With.Swap` | Koszul 符号付き交換と左右の比較の整合性 |
| `With.LeftInjection` / `RightInjection` | 直和成分上の公式 |
| `HomComplex.Over.Homotopy.Native` | 鎖ホモトピーから任意係数の Hom 余鎖ホモトピーへの反変な移行 |
| `HomComplex.Over.Equivalence.Native` | 鎖ホモトピー同値から得る余鎖の比較写像と、両合成の余鎖ホモトピー |

二重複体の基盤は [double_complexes](../double_complexes/README.md)、次数ごとに台集合が変わる利用例は [Cohomology.ref](../../../geometry/coordinate_calculus/src/Cohomology.ref) にある。
