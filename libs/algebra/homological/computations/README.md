# ホモロジー代数の計算と積

有限複体のホモロジー計算、テンソル余鎖複体、Künneth 同型を扱う。
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

`homological_algebra.FieldFinite.Over` は各次数の有限座標空間、微分、有界性を持つ余鎖複体を扱う。
`Of.At` はサイクル・境界・コホモロジーの射影性と、それらの短完全列を公開する。
`Of.splittingExistence` は全次数の分裂の存在を示す。
`Of.Split` は選んだ分裂から、零微分のコホモロジー複体への写像と逆方向の写像を構成する。
`homological_algebra.Finite.Bounded.Mapping` は全次数の整数行列から鎖写像を構成する。
`At.With` の `coordinateRuntime` と `onFactorClasses` は計算した生成元の間の行列と元のホモロジー写像との対応を返す。
`intertwines` は有界複体のホモロジー同型が誘導写像と可換になることを示す。

## 自然数次数のテンソル余鎖複体

`homological_algebra.TensorCochain.Over` は可換環上の二重余鎖複体と有限対角直和による total を構成する。
`Tensor` は二つの余鎖複体から、水平微分を左因子、垂直微分を右因子に作用させる二重複体を作る。
`Total` の微分は水平微分と第一次数の符号を掛けた垂直微分の和であり、二乗零を直和の普遍性で証明する。
`TensorMapping` は両因子の余鎖写像から total 上の余鎖写像を構成する。
`HorizontalHomotopy.With` は水平ホモトピーから total 上の余鎖ホモトピーを作り、`HomotopyLeft.With` はテンソル積の左因子のホモトピーをこの構成に接続する。
`Swap` は第一・第二次数を交換した二重複体の total へ、成分 \(p,q\) に \((-1)^{pq}\) を掛ける交換写像を作り、逆写像と各次数のコホモロジー同型を返す。
`Map.Inverse.With` は項ごとの逆写像から逆向きの二重複体写像を構成し、total とコホモロジー上の逆の法則を証明する。

`homological_algebra.TensorCochain.Over.CycleProduct` はサイクル代表元のテンソルから total のコホモロジー類を作り、双線形性を証明する。
`RightCycleBoundary` は右側のサイクルが境界なら積の類が零になることを示す。
`LeftCycleBoundary` は左側の境界について同じ消滅を証明する。
`Exterior.map` は両側の境界による消滅を使い、コホモロジーのテンソル積から total のコホモロジーへの準同型を構成する。
`CycleProductNaturality.With.Exterior.naturality` はこの外積が両因子の余鎖写像による誘導写像と可換になることを示す。

検査方法と関連パッケージは [ライブラリ一覧](../../../README.md) を参照。
