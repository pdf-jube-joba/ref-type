# 複素スピノル表現

複素外代数上の生成・消滅作用から Clifford 代数と Spin、Spin-c の表現を構成する。
内積は第1引数について共役線形、第2引数について線形で、実 Clifford 乗算は自己随伴である。
有限次元の構成は零次元を含む。

`Complex.Dimension[n]` は \(\mathbb C^n\) の全次数の外積形式をスピノル空間とする。
`TotalInner.Adjoint` は生成作用と消滅作用の随伴関係を、`TotalInner.Adjoint.Isometry.PinAction` は Spin-c 作用の等長性を与える。
`RealCoordinates.Clifford.Spin.Phase` は標準実 \(2n\) 次元 Clifford 代数からの Spin-c 作用と直交射影、行列式文字を与える。

`UnitaryOrthogonal.CanonicalLift` の `homomorphism` は、真空を固定する条件で定まる \(U(n)\to\operatorname{Spin}^c(2n)\) である。
`CanonicalLift.FockWords.Complete.actionEqual` はそのスピノル作用と外代数への引き戻し作用を比較する。
`Pairing.Determinant.correspondence` は Spin-c の行列式文字がユニタリ写像の逆行列式に等しいことを示す。
引き戻しを採用しているため、最高次数には逆行列式が作用する。

`Topology.topology` は全次数の評価写像が定めるスピノル空間の位相である。
`Families.liftedOrbitContinuous` は連続なユニタリ族に対して、各固定スピノルの標準持ち上げによる軌道がこの位相で連続であることを示す。
標準持ち上げ自体の Spin-c の多様体位相に関する連続性と滑らかさは未証明である。

`Over.Direct.Total.comparison` は左右のスピノルのテンソル積から直和の外代数への線形写像である。
`Over.Direct.Total.Isomorphism` は右側と直和に有限基底を指定すると、この比較写像を前向きの写像とする線形同型を構成する。
単射性は左右の縮約で取り出した係数によって核を分離し、全射性は真空からの生成で証明する。
`Over.Direct.Total.Grading.intertwines` は偶奇次数の保存を、`Complex.Graded.Comparison.Algebra.intertwining` は Clifford 代数全体の作用との整合性を示し、`Over.Direct.Total.Vacuum.Words` は生成作用で作った状態の対応を与える。

[Examples](src/Examples.ref) に一次元の平方・随伴公式、標準持ち上げと行列式文字の例があり、[ZeroTensor](src/Examples/ZeroTensor.ref) は零次元のテンソル比較の往復を検査する。

```sh
target/debug/cli libs/algebra/spinor_representations --memory-mib 8192 --cache-stats --no-progress
```
