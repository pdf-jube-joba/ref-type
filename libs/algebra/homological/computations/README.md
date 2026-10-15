# ホモロジー代数の計算と積

有限自由整数複体のホモロジー計算、普遍係数短完全列、整数 Künneth を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`homological_algebra.Finite.Pair` は隣接する整数境界行列と二乗零の法則を持つ。
`Of.coordinateIsomorphism` は核内の境界像で割ったホモロジーを、Smith 標準形から得た核の座標での余核へ移す。
`matrixCorrespondence` はこの像の行列を、実行可能な基底変更と先頭行の除去で計算した行列に結び付ける。
`homological_algebra.Finite.Compute.Run` は二段階の Smith 計算を実行し、自由階数、対角因子、元の座標での生成行列と逆座標行列を返す。
`homological_algebra.Finite.Pair.Of.Result` はこの実行結果と、元のサイクルの商から巡回加群の積への双方向の準同型および逆の法則を持つ。
`computedForwardOnClass` は返された逆座標行列の作用を商の写像に結び付ける。
`homological_algebra.Finite.Mapping.With` は複体写像を生成元の座標へ移し、実際の行列積で得た係数とホモロジーの誘導写像が一致することを示す。
`homological_algebra.Finite.Bounded` は整数次数の階数・境界行列と、有界性・二乗零の法則を持つ。
`Of.At.Result` は通常の整数次数ホモロジーの商との同型を返す。
`Of.Dual` は転置した境界行列から整数次数の余鎖複体を作り、`At.Result` はそのコホモロジーの商との同型を返す。
`Of.BasisChange.With` は微分を \(T_{n-1}d_nT_n^{-1}\) に変換し、二乗零を保つ有界複体、鎖同型とホモロジー同型を構成する。

`homological_algebra.Finite.Bounded.Mapping` は全次数の整数行列から鎖写像を構成する。
`At.With` の `coordinateRuntime` と `onFactorClasses` は計算した生成元の間の行列と元のホモロジー写像との対応を返す。
`intertwines` は有界複体のホモロジー同型が誘導写像と可換になることを示す。

`Finite.Bounded.Of.At.UniversalCoefficient.CohomologyKernel.sequence` は、有限自由整数複体と任意の整数加群係数について、Ext¹・コホモロジー・Hom の普遍係数短完全列を返す。
`UniversalCoefficient.Tensor.Projection.Exactness.Derived.sequence` は、ホモロジーのテンソル・係数付きホモロジー・Tor₁ の短完全列を返す。
前者の `splitting` と後者の `isomorphism` は Smith 計算から選んだ分裂による直和表示である。
`UniversalCoefficient.rightInverse` は評価写像の全射性を、`Tensor.Boundaries.onCycles` はホモロジー側の包含をサイクルのテンソル上の公式へ結び付ける。
[利用例](../../../../libs/algebra/homological/concrete_complexes/src/Finite/Bounded/UniversalCoefficient.ref)は、非対角の三項整数複体、任意次数と係数、零次・負次数・\(\mathbb Z/2\) 係数に対してこれらの短完全列と分裂を検査する。

`UniversalCoefficient.Abstract` は共通の射影的な構成と有限整数複体の短完全列を同一視する。
`Finite.Bounded.Mapping.At.With.UniversalCoefficient.On` は複体写像と係数写像について Ext¹ 側の包含まで含めた可換図式を、`TensorUniversalCoefficient.On` は Tor₁ 側の射影まで含めた可換図式を返す。
それぞれの `Derived.functorAgreement` は端の写像を既存の Ext・Tor の両変数の写像と同一視する。
`smithNaturality` は Smith 分裂による直和座標と誘導写像の対応を、`valuesOnComputedGenerators` と `leftOnComputedGenerators` は計算した生成元上の自然性を示す。
`Tensor.Projection.Exactness.Derived.Projective.isomorphism` は射影係数について包含写像を同型にする。

`homological_algebra.Kunneth.Integer.Theorem[C, D].At[n].sequence` は、有界有限自由整数鎖複体について次の短完全列を公開する。

\[
0\longrightarrow\bigoplus_{p+q=n}H_p(C)\otimes H_q(D)
\longrightarrow H_n(C\otimes D)
\longrightarrow\bigoplus_{p+q=n-1}\operatorname{Tor}^{\mathbb Z}_1(H_p(C),H_q(D))
\longrightarrow0.
\]

`inclusionEq` は左の写像を `CoreTerms.At.exterior` と、`projectionEq` は右の写像を接続写像から得た `Theorem.Projection.map` と同一視する。
`selectedSplitting` はホモロジーのテンソル項と Tor 項の直和表示を、`smithSplitting` はテンソル項を Smith 座標へ移した直和表示を返す。
`Integer.Assertions.ExactTheorem.theorem` は、複体と次数を量化した、標準外積を左の写像とする短完全列の存在を公開する。
`Integer.Assertions` の `Naturality.theorem`、`Splitting.theorem`、`SmithSplitting.theorem` は、両因子の自然性、選んだ分裂、Smith 分裂の存在をそれぞれ全称量化して公開する。
`Mapping.At.Component.onComputedGenerators` は計算した生成元上のテンソル写像を、両因子の座標行列の作用に結び付ける。

`Integer.TensorSequence[C, D].Mapping[E, F].With[f, g]` はサイクル・境界の写像から三つのテンソル鎖写像 `left`・`middle`・`right` を作る。
`diagram` は `tensor_chains.TensorChain.Over.TensorSquare` を使って短完全列の左右の四角形を構成する。
`Integer.Theorem[C, D].Mapping[E, F].With[f, g].At[n]` は、端の `tensorMap`・`torMap` と中央の `homologyMap` を持ち、`leftSquare`・`rightSquare` と `diagram` で最終的な Künneth 短完全列全体の自然性を公開する。
右の四角形は鎖複体の接続写像の自然性を `TorDiagonal.Mapping.With.naturality` により標準の Tor 項へ移して得る。

体係数の有限余鎖複体と標準外積同型は [field_kunneth](../field_kunneth/README.md)、整数次数のテンソル鎖複体は [tensor_chains](../tensor_chains/README.md) にある。

検査方法と関連パッケージは [ライブラリ一覧](../../../README.md) を参照。
