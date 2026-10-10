# ホモロジー代数

`Cochain.Over[R := R, ring := ring]` は環上の加群の自然数次数の余鎖複体を扱う。
各次数の台集合を `Family` の型値定義で返し、微分の線形性と二乗零を `Complex` にまとめる。
`Cohomology` は微分の核を境界の部分加群で割り、閉元の類・類の等式判定・完全元の零性と商の普遍性を公開する。
次数零の境界は零部分加群である。
余鎖写像はコホモロジー上の準同型へ降り、恒等写像と合成に整合する。

`Integer.Over[R := R, ring := ring]` は `std.Arithmetic.Int` の整数を次数に用いる。
各次数のコホモロジーは直前の微分の像を現在の微分の核の内部へ移した商である。
`Cochain.Over.ZeroExtension[C := C]` は非負次数で元の複体と同型、負次数で零空間となる整数次数の複体を構成する。
`Cochain.Over.Recovery` は非負次数への制限との往復とコホモロジー同型を、`BoundaryZero` と `BoundarySuccessor` は零次と正次数での境界の一致を公開する。
`PositiveCohomology[n].isomorphism` は整数次数 \(n\) の商と元の自然数次数 \(n\) の商を直接結ぶ。
`NegativeCohomology[n].isomorphism` は負次数 \(-n-1\) のコホモロジーと零空間の同型を返す。
`Integer.Over.Map` の誘導写像は、閉元と境界を保存することを証明して商へ降ろされ、恒等写像と合成に整合する。

`Chain.Over` は整数次数の鎖複体 \(d_n:C_n\to C_{n-1}\) を扱う。
`At` はサイクル・境界・ホモロジーの加群を、`Map.At` は誘導準同型と恒等・合成の法則を公開する。
`Homotopy` は \(f-g=dh+hd\) の規約による鎖ホモトピーを持ち、`Homotopy.At.onHomology` は誘導写像の一致を示す。
`Equivalence.At` は鎖ホモトピー同値からホモロジーの同型を作る。
`ZeroDifferential.At` は零微分の複体のホモロジーと各項との同型を返す。
`Shift` は微分を \(-d\) とするシフトを、`Cone` は \(D_n\oplus C_{n-1}\) 上の cone とその次数ごとの短完全列を構成する。
`Chain.Over.Shift.Homology` は符号を含むホモロジー同型を返す。
`Cone[C := C, D := D].On[f := f]` は複体を具体化した後で鎖写像を受け取る。
`ConeIdentity` は恒等写像の cone の具体的な収縮と、全次数でのホモロジー消滅を公開する。
`Zero` と `Concentrated` は零複体と単一次数に集中した複体を構成し、零・中心・中心以外のホモロジー同型を返す。
`NonnegativeChain.Over.ZeroExtension` は `DegreeZeroHomology`・`PositiveHomology`・`NegativeHomology` で元のホモロジーとの同型と負次数の消滅を公開する。
`Chain.Over.Reverse` と `Reversal.Over.ToChain` は整数の符号反転による両方向の変換を提供する。
`ModuleCategory.Over.On` は集合で添字付けられた加群族の全準同型から前加法圏を作る。
`ShortExactCategory.Over.On` は複体の短完全列の族と、その可換図式を射とする圏を作る。
`Degree.sourceFunctor`・`targetFunctor` は両端のホモロジー関手を、`Degree.transformation` は接続準同型を成分とする自然変換を返す。

`Finite.Pair` は隣接する整数境界行列と二乗零の法則を持つ。
`Of.coordinateIsomorphism` は核内の境界像で割ったホモロジーを、Smith 標準形から得た核の座標での余核へ移す。
`matrixCorrespondence` はこの像の行列を、実行可能な基底変更と先頭行の除去で計算した行列に結び付ける。
`Finite.Compute.Run` は二段階の Smith 計算を実行し、自由階数、対角因子、元の座標での生成行列と逆座標行列を返す。
`Finite.Pair.Of.Result` はこの実行結果と、元のサイクルの商から巡回加群の積への双方向の準同型および逆の法則を持つ。
`computedForwardOnClass` は返された逆座標行列の作用を商の写像に結び付ける。
`Finite.Mapping.With` は複体写像を生成元の座標へ移し、実際の行列積で得た係数とホモロジーの誘導写像が一致することを示す。
`Finite.Bounded` は整数次数の階数・境界行列と、有界性・二乗零の法則を持つ。
`Of.At.Result` は通常の整数次数ホモロジーの商との同型を返す。
`Of.Dual` は転置した境界行列から整数次数の余鎖複体を作り、`At.Result` はそのコホモロジーの商との同型を返す。
`Of.BasisChange.With` は微分を \(T_{n-1}d_nT_n^{-1}\) に変換し、二乗零を保つ有界複体、鎖同型とホモロジー同型を構成する。

`Resolution.Over` は非負次数の射影分解と、比較写像・比較写像の鎖ホモトピーによる一意性を扱う。
`Resolution.Over.ShortExact.Sequence` は増大写像と整合する分解の短完全列を束ねる。
`Morphism.With.existence` は係数の可換図式を鎖複体の可換図式へ持ち上げる。
`NonnegativeChain.Over.ShortExact.Morphism.Straighten` は比較写像をホモトピーで補正し、増大写像を保った可換図式を構成する。
`ResolutionTensor.Over.Of.With` は射影加群と指定した射影分解のテンソルから分解を構成し、増大写像の全射性、完全性と各項の射影性を証明する。
`Ext.Over.Of` と `Tor.Over.Of` は指定した射影分解から得た加群を各次数に返す。
`Independence` は同じ加群の別の分解との同型を、`DegreeZero` は Hom とテンソル積との零次の同型を提供する。

`Ext.Over.Extension.With` は指定した射影分解の Ext¹ を、第1シジジーからの準同型の商と同型にする。
`OfExtension.With.extClass` は短完全拡大に対応する Ext¹ の類を返す。
`RepresentationClass` は押し出しで代表となる拡大を作り、`represented` は全類の代表の存在を示す。
`Compare.correspondence` は類の一致と、両端の加群を固定する拡大の同型との対応を証明する。
`OfExtension.With.Split.extZero` は切断を持つ拡大が零類になることを示す。

`FieldFinite.Over` は各次数の有限座標空間、微分、有界性を持つ余鎖複体を扱う。
`Of.At` はサイクル・境界・コホモロジーの射影性と、それらの短完全列を公開する。
`Of.splittingExistence` は全次数の分裂の存在を示す。
`Of.Split` は選んだ分裂から、零微分のコホモロジー複体への写像と逆方向の写像を構成する。
`Cochain.Over.ZeroDifferential.At` は零微分の複体のコホモロジーと各項との同型を返す。
`TensorComplex.Over.Square.With.naturality` はテンソル積が鎖写像の可換図式を保つことを示す。

一般の加群・核・像・商は `algebra.Module` を利用する。
実数上の具体化と、次数ごとに台集合が変わる利用例は [Cohomology.ref](../../tests/projects/manifolds-de-rham/src/Cohomology.ref) にある。

```sh
target/debug/cli libs/homological_algebra --module homological_algebra --full-check-local --diagnostics compact
target/debug/cli tests/projects/homological-algebra --module homological_algebra_tests --full-check-local --diagnostics compact
```

`Finite.Bounded.Mapping` は全次数の整数行列から鎖写像を構成する。
`At.With` の `coordinateRuntime` と `onFactorClasses` は計算した生成元の間の行列と元のホモロジー写像との対応を返す。
`intertwines` は有界複体のホモロジー同型が誘導写像と可換になることを示す。

## 自然数次数のテンソル余鎖複体

`TensorCochain.Over` は可換環上の二重余鎖複体と有限対角直和による total を構成する。
`Tensor` は二つの余鎖複体から、水平微分を左因子、垂直微分を右因子に作用させる二重複体を作る。
`Total` の微分は水平微分と第一次数の符号を掛けた垂直微分の和であり、二乗零を直和の普遍性で証明する。
`TensorMapping` は両因子の余鎖写像から total 上の余鎖写像を構成する。
`HorizontalHomotopy.With` は水平ホモトピーから total 上の余鎖ホモトピーを作り、`HomotopyLeft.With` はテンソル積の左因子のホモトピーをこの構成に接続する。
`Swap` は第一・第二次数を交換した二重複体の total へ、成分 \(p,q\) に \((-1)^{pq}\) を掛ける交換写像を作り、逆写像と各次数のコホモロジー同型を返す。
`Map.Inverse.With` は項ごとの逆写像から逆向きの二重複体写像を構成し、total とコホモロジー上の逆の法則を証明する。

`CochainEquivalence.Over.Of.With` は二つの写像と両合成のホモトピーから、全次数のコホモロジー同型を返す。
体上の有界有限自由余鎖複体では `FieldFinite.Over.Of.Split.Contraction` が恒等写像から代表元の包含と射影の合成へのホモトピーを構成する。
`Split.At` は微分が零のコホモロジー族と元の複体のコホモロジーの同型を返す。

`TensorCochain.Over.CycleProduct` はサイクル代表元のテンソルから total のコホモロジー類を作り、双線形性を証明する。
`RightCycleBoundary` は右側のサイクルが境界なら積の類が零になることを示す。
`LeftCycleBoundary` は左側の境界について同じ消滅を証明する。
`Exterior.map` は両側の境界による消滅を使い、コホモロジーのテンソル積から total のコホモロジーへの準同型を構成する。
`CycleProductNaturality.With.Exterior.naturality` はこの外積が両因子の余鎖写像による誘導写像と可換になることを示す。
