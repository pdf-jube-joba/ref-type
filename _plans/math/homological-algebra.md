# ホモロジー代数の比較・自然性・Künneth

実装済み。
公開 API と構成は各 README を参照。

- [double_complexes](../../libs/algebra/homological/double_complexes/README.md)：二重 total の完全性と交換。
- [resolutions](../../libs/algebra/homological/resolutions/README.md)：二つの分解と片側の分解の比較。
- [derived_functors](../../libs/algebra/homological/derived_functors/README.md)：Tor の両側の比較、普遍係数の自然性。
- [tensor_chains](../../libs/algebra/homological/tensor_chains/README.md)：整数次数の total と外積。
- [field_kunneth](../../libs/algebra/homological/field_kunneth/README.md)：体係数の標準外積同型。
- [homological_algebra](../../libs/algebra/homological/computations/README.md)：有限整数複体の普遍係数・Künneth 短完全列。

| 構成 | API |
| --- | --- |
| Tor の両側の比較 | `derived_functors.Tor.Over.Balance`、`ShortExactFirst.With.On.Balance` |
| 普遍係数短完全列の自然性 | `Finite.Bounded.Mapping.At.With.UniversalCoefficient.On`、`TensorUniversalCoefficient.On` |
| 整数 Künneth 短完全列 | `Kunneth.Integer.Theorem.At.sequence`、`inclusionEq`、`projectionEq` |
| 整数 Künneth の自然性 | `Kunneth.Integer.TensorSequence.Mapping.With.diagram`、`Theorem.Mapping.With.At.diagram` |
| 選んだ整数 Künneth 分裂 | `Kunneth.Integer.Theorem.At.selectedSplitting`、`smithSplitting` |
| 全称量化した整数定理 | `Kunneth.Integer.Assertions` の `ExactTheorem`・`Naturality`・`Splitting`・`SmithSplitting` が持つ `theorem` |
| 標準の体係数 Künneth 同型 | `field_kunneth.Kunneth.Field.Of.Canonical`、`Mapping.With.At`、`Symmetry`、`Unit` |

[concrete_complexes](../../libs/algebra/homological/concrete_complexes/README.md) に、非零の Tor、自然性、基底変更、分裂、交換符号・単位の利用例がある。
検査には共有キャッシュを使い、大きな比較写像は `--memory-mib 7168`、整数 Künneth は `15360`、その利用例は `15872` を指定する。
特異理論への接続は [次の計画](singular-cohomology.md) を参照。
