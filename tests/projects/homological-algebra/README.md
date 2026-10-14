# ホモロジー代数の証明付き利用例

`BasicComplexes` は零複体、集中した加群、恒等写像の cone と符号を検査する。
`Cyclic` は \(\mathbb Z/2\) と \(\mathbb Z/4\) の Ext¹・Tor₁、および係数写像を計算する。
`Cyclic.Extensions` は Ext¹ の全類の拡大による表示と、分裂拡大の零類を扱う。
`Cyclic.ProjectiveCoefficient` は第二変数の射影性による消滅定理を使い、\(\operatorname{Tor}_n(\mathbb Z/2,\mathbb Z)=0\)、\(n>0\) を検査する。
`ExactSequences` は \(0\to\mathbb Z\to\mathbb Z^2\to\mathbb Z\to0\) と係数倍の可換図式から、比較同型、接続写像の自然性と自然変換を利用する。
`Finite` は非対角の三項整数複体について、核の座標内の像、基底変更、商との同型と誘導写像を計算する。
`Finite.Bounded.UniversalCoefficient` はこの複体の Ext¹・Hom とテンソル・Tor₁ の普遍係数短完全列、選んだ分裂、評価写像とサイクル上の包含を検査する。
零次・負次数と \(\mathbb Z/2\) 係数への具体化を含む。
`Field` は体上の有界有限自由余鎖複体を構成し、一般加群のコホモロジーと `linear_algebra` の商との同型を検査する。

```sh
target/debug/cli tests/projects/homological-algebra --module homological_algebra_tests --full-check-local --diagnostics compact
target/debug/cli tests/projects/homological-algebra --module homological_algebra_tests.Cyclic.ProjectiveCoefficient --diagnostics compact
target/debug/cli tests/projects/homological-algebra --module homological_algebra_tests.Finite.Bounded.UniversalCoefficient --diagnostics compact
```
