# 体係数の標準外積と Künneth 同型

有界有限自由体係数余鎖複体と、分裂の選択によらない標準外積同型を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`field_kunneth.FieldFinite.Over` は各次数の有限座標空間、微分、有界性を持つ余鎖複体を扱う。
`Of.At` はサイクル・境界・コホモロジーの射影性と、それらの短完全列を公開する。
`Of.splittingExistence` は全次数の分裂の存在を示す。
`Of.Split` は選んだ分裂から、零微分のコホモロジー複体への写像と逆方向の写像を構成する。
## 自然数次数のテンソル余鎖複体

`field_kunneth.TensorCochain.Over` は可換環上の二重余鎖複体と有限対角直和による total を構成する。
`Tensor` は二つの余鎖複体から、水平微分を左因子、垂直微分を右因子に作用させる二重複体を作る。
`Total` の微分は水平微分と第一次数の符号を掛けた垂直微分の和であり、二乗零を直和の普遍性で証明する。
`TensorMapping` は両因子の余鎖写像から total 上の余鎖写像を構成する。
`HorizontalHomotopy.With` は水平ホモトピーから total 上の余鎖ホモトピーを作り、`HomotopyLeft.With` はテンソル積の左因子のホモトピーをこの構成に接続する。
`Swap` は第一・第二次数を交換した二重複体の total へ、成分 \(p,q\) に \((-1)^{pq}\) を掛ける交換写像を作り、逆写像と各次数のコホモロジー同型を返す。
`Map.Inverse.With` は項ごとの逆写像から逆向きの二重複体写像を構成し、total とコホモロジー上の逆の法則を証明する。

`field_kunneth.TensorCochain.Over.CycleProduct` はサイクル代表元のテンソルから total のコホモロジー類を作り、双線形性を証明する。
`RightCycleBoundary` は右側のサイクルが境界なら積の類が零になることを示す。
`LeftCycleBoundary` は左側の境界について同じ消滅を証明する。
`Exterior.map` は両側の境界による消滅を使い、コホモロジーのテンソル積から total のコホモロジーへの準同型を構成する。
`CycleProductNaturality.With.Exterior.naturality` はこの外積が両因子の余鎖写像による誘導写像と可換になることを示す。
`IndexedExterior` は次数の等式を使って各外積を任意の対角直和の成分に移し、`IndexedCycleProductNaturality` はその代表元上の自然性を示す。
`TensorSymmetry.At.Component.onClass` と `inverseOnClass` は、交換同型とその逆が外積の類に \((-1)^{pq}\) を掛けて因子を交換することを示す。

`Kunneth.Field.Assertions.standardIsomorphism` は二つの有限複体と次数を命題内で量化し、順方向が標準外積に等しい同型の存在を返す。
`Assertions.naturality` と `inverseNaturality` は四つの有限複体・両因子の余鎖写像・次数を量化した可換性の定理である。
`Kunneth.Field.Of` は二つの有界有限自由体係数余鎖複体を入力に保持する。
`Canonical.exterior` は各成分の `Exterior.map` を有限対角直和の普遍性でまとめた写像であり、`Component.onClass` は代表元上の外積の公式を、`characterized` はその公式による一意性を返す。
`With.At.ExteriorComparison.backwardExterior` は、分裂から構成した従来の同型の逆がこの標準外積と一致することを証明する。
`Canonical.isomorphism` と `At.isomorphism` は互いに逆向きの標準 Künneth 同型であり、`Canonical.SplittingChange` は分裂を変えたときの両向きの写像の一致を示す。
`Symmetry.compatibility` は有限複体の標準外積を交換したときの \((-1)^{pq}\) の公式を返す。
`Mapping.With.At.naturality` と `inverseNaturality` は両因子の余鎖写像による対角直和の写像と、標準同型の両向きとの可換性を返す。
`TensorCochain.Over.Unit` は零次に一つ、そのほかの次数に零個の座標を持つ有限座標加群から単位複体を構成する。零次の唯一の座標での評価により係数環と同一視し、定数一のベクトルを単位元とする。
`With.Cohomology.exteriorUnit` と `RightCohomology.exteriorUnit` は左右の単位縮約が単位類との外積を元のコホモロジー類へ戻すことを示し、`Kunneth.Field.Unit` は有限自由体係数複体への適用を公開する。

```sh
cargo run -p cli -- libs/algebra/homological/field_kunneth --module field_kunneth
```
