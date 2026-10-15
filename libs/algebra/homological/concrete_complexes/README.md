# ホモロジー代数の証明付き具体的な複体

`BasicComplexes` は零複体、集中した加群、恒等写像の cone と符号を検査する。
`Cyclic` は \(\mathbb Z/2\) と \(\mathbb Z/4\) の Ext¹・Tor₁、および係数写像を計算する。
`Cyclic.Extensions` は Ext¹ の全類の拡大による表示と、分裂拡大の零類を扱う。
`Cyclic.ProjectiveCoefficient` は第二変数の射影性による消滅定理を使い、\(\operatorname{Tor}_n(\mathbb Z/2,\mathbb Z)=0\)、\(n>0\) を検査する。
`Cyclic.DoubleTensor` は \(\mathbb Z/2\) の二つの分解のテンソル total と比較鎖写像を使い、二次の生成元の境界の符号と二乗零を検査する。
`Cyclic.DoubleTensor.Balanced` は total の両側の比較ホモロジー同型と、native Tor の同型を利用する。
`Cyclic.BalancedExact` は \(0\to\mathbb Z/2\to\mathbb Z/4\to\mathbb Z/2\to0\) の Horseshoe 分解を構成し、`With.connectingNaturality` で Tor の変数交換と接続写像との整合性を検査する。
`ExactSequences` は \(0\to\mathbb Z\to\mathbb Z^2\to\mathbb Z\to0\) と係数倍の可換図式から、比較同型、接続写像の自然性と自然変換を利用する。
`Finite` は非対角の三項整数複体について、核の座標内の像、基底変更、商との同型と誘導写像を計算する。
`Finite.Bounded.UniversalCoefficient` はこの複体の Ext¹・Hom とテンソル・Tor₁ の普遍係数短完全列、選んだ分裂、評価写像とサイクル上の包含を検査する。
零次・負次数と \(\mathbb Z/2\) 係数への具体化を含む。
`Finite.Bounded.IntegerTor.isomorphism` は自己テンソル積の全次数3に現れる \(\operatorname{Tor}^{\mathbb Z}_1(H_1,H_1)\) を \(\mathbb Z/2\) と同型にし、`generator`・`onGenerator` はその標準生成元の対応を与える。
`Finite.Bounded.IntegerTensor` は全次数3の整数 Künneth 短完全列、標準外積との一致を利用する。
`IntegerTensor.Selected` は選んだ分裂と Smith 座標での分裂を具体化する。
`Selected.liftedGenerator`・`Selected.projectionOnGenerator` は上の Tor 生成元をテンソル積複体のホモロジーへ持ち上げ、射影で元に戻ることを示す。
`IntegerTensorNaturality.diagram` は左因子の非自明な基底変更と右因子の恒等写像について、最終的な短完全列の両方の四角形を具体化する。
`Field` は体上の有界有限自由余鎖複体を構成し、一般加群のコホモロジーと `linear_algebra` の商との同型を検査する。
`Field.Tensor` は標準 Künneth 同型と外積の代表元公式、分裂変更による両向きの写像の一致、交換写像と左右の単位整合性を利用する。

```sh
target/debug/cli libs/algebra/homological/concrete_complexes --module concrete_complexes --cache-dir libs/refcache --memory-mib 15872 --batch-seconds 60 --diagnostics compact
target/debug/cli libs/algebra/homological/concrete_complexes --module concrete_complexes.Cyclic.ProjectiveCoefficient --diagnostics compact
target/debug/cli libs/algebra/homological/concrete_complexes --module concrete_complexes.Finite.Bounded.UniversalCoefficient --diagnostics compact
```
