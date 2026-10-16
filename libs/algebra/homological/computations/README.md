# ホモロジー代数の計算と積

import 名は `homological_algebra`。
有界有限自由整数複体のホモロジー、普遍係数、整数 Künneth を扱う。

| module | 内容 |
| --- | --- |
| `Finite.Pair.Of` | 核内の境界像を Smith 座標の余核へ移す同型 |
| `Finite.Compute.Run` | 二段階の Smith 計算、自由階数・対角因子・生成行列と逆座標 |
| `Finite.Pair.Of.Result` | サイクルの商と巡回加群の積の往復、生成元上の公式 |
| `Finite.Bounded.Of.At` / `Of.Dual` | 整数次数のホモロジー / 転置によるコホモロジー |
| `Of.BasisChange.With` / `Mapping.At.With` | 基底変更、鎖写像、計算した座標行列と誘導写像の一致 |
| `UniversalCoefficient.CohomologyKernel.sequence` | Ext¹・コホモロジー・Hom の短完全列 |
| `UniversalCoefficient.Tensor.Projection.Exactness.Derived.sequence` | テンソル・係数付きホモロジー・Tor₁ の短完全列 |
| `Finite.Bounded.Mapping.At.With.UniversalCoefficient.On` / `TensorUniversalCoefficient.On` | 複体写像・係数写像による短完全列全体の自然性 |
| `Kunneth.Integer.Theorem.At.sequence` | 標準外積と Tor 射影を持つ整数 Künneth 短完全列 |
| `Theorem.At.selectedSplitting` / `smithSplitting` | 選んだ分裂と Smith 座標の直和表示 |
| `Theorem.Mapping.With.At.diagram` | 両因子の写像による短完全列の自然性 |
| `Kunneth.Integer.Assertions` | 全称量化した完全性・自然性・分裂の定理 |

\[
0\longrightarrow\bigoplus_{p+q=n}H_p(C)\otimes H_q(D)
\longrightarrow H_n(C\otimes D)
\longrightarrow\bigoplus_{p+q=n-1}\operatorname{Tor}^{\mathbb Z}_1(H_p(C),H_q(D))
\longrightarrow0.
\]

`inclusionEq`・`projectionEq` は標準写像との一致、`onComputedGenerators` は計算した生成元上の作用を返す。
普遍係数の `Derived.functorAgreement` は端の写像を既存の Ext・Tor の写像と同一視する。
[体係数](../field_kunneth/README.md)、[整数次数の total](../tensor_chains/README.md)、[利用例](../concrete_complexes/README.md) を参照。
