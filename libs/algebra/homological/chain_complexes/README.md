# 鎖複体と余鎖複体

自然数・整数次数の複体、ホモロジー、写像・ホモトピー・複体の圏を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`chain_complexes.Cochain.Over[R := R, ring := ring]` は環上の加群の自然数次数の余鎖複体を扱う。
各次数の台集合を `Family` の型値定義で返し、微分の線形性と二乗零を `Complex` にまとめる。
`Cohomology` は微分の核を境界の部分加群で割り、閉元の類・類の等式判定・完全元の零性と商の普遍性を公開する。
次数零の境界は零部分加群である。
余鎖写像はコホモロジー上の準同型へ降り、恒等写像と合成に整合する。

`chain_complexes.Integer.Over[R := R, ring := ring]` は `std.Arithmetic.Int` の整数を次数に用いる。
各次数のコホモロジーは直前の微分の像を現在の微分の核の内部へ移した商である。
`chain_complexes.Cochain.Over.ZeroExtension[C := C]` は非負次数で元の複体と同型、負次数で零空間となる整数次数の複体を構成する。
`chain_complexes.Cochain.Over.Recovery` は非負次数への制限との往復とコホモロジー同型を、`BoundaryZero` と `BoundarySuccessor` は零次と正次数での境界の一致を公開する。
`PositiveCohomology[n].isomorphism` は整数次数 \(n\) の商と元の自然数次数 \(n\) の商を直接結ぶ。
`NegativeCohomology[n].isomorphism` は負次数 \(-n-1\) のコホモロジーと零空間の同型を返す。
`chain_complexes.Integer.Over.Map` の誘導写像は、閉元と境界を保存することを証明して商へ降ろされ、恒等写像と合成に整合する。

`chain_complexes.Chain.Over` は整数次数の鎖複体 \(d_n:C_n\to C_{n-1}\) を扱う。
`At` はサイクル・境界・ホモロジーの加群を、`Map.At` は誘導準同型と恒等・合成の法則を公開する。
`Homotopy` は \(f-g=dh+hd\) の規約による鎖ホモトピーを持ち、`Homotopy.At.onHomology` は誘導写像の一致を示す。
`Equivalence.At` は鎖ホモトピー同値からホモロジーの同型を作る。
`ZeroDifferential.At` は零微分の複体のホモロジーと各項との同型を返す。
`Shift` は微分を \(-d\) とするシフトを、`Cone` は \(D_n\oplus C_{n-1}\) 上の cone とその次数ごとの短完全列を構成する。
`chain_complexes.Chain.Over.Shift.Homology` は符号を含むホモロジー同型を返す。
`Cone[C := C, D := D].On[f := f]` は複体を具体化した後で鎖写像を受け取る。
`ConeIdentity` は恒等写像の cone の具体的な収縮と、全次数でのホモロジー消滅を公開する。
`Zero` と `Concentrated` は零複体と単一次数に集中した複体を構成し、零・中心・中心以外のホモロジー同型を返す。
`chain_complexes.Chain.Over.Reverse` と `chain_complexes.Reversal.Over.ToChain` は整数の符号反転による両方向の変換を提供する。
`chain_complexes.ModuleCategory.Over.On` は集合で添字付けられた加群族の全準同型から前加法圏を作る。
`chain_complexes.ShortExactCategory.Over.On` は複体の短完全列の族と、その可換図式を射とする圏を作る。
`Degree.sourceFunctor`・`targetFunctor` は両端のホモロジー関手を、`Degree.transformation` は接続準同型を成分とする自然変換を返す。

`chain_complexes.Cochain.Over.ZeroDifferential.At` は零微分の複体のコホモロジーと各項との同型を返す。
`chain_complexes.CochainEquivalence.Over.Of.With` は二つの写像と両合成のホモトピーから、全次数のコホモロジー同型を返す。
体上の有界有限自由余鎖複体では `field_kunneth.FieldFinite.Over.Of.Split.Contraction` が恒等写像から代表元の包含と射影の合成へのホモトピーを構成する。
`Split.At` は微分が零のコホモロジー族と元の複体のコホモロジーの同型を返す。

検査方法と関連パッケージは [ライブラリ一覧](../../../README.md) を参照。

`Chain.Over.Map.Kernel` は鎖写像の項ごとの核を複体として構成する。
項ごとの全射性と、核のサイクルが核の中の境界になることから、比較写像がホモロジー同型を誘導することを証明する。
