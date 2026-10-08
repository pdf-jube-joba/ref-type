# ホモロジー代数

`Cochain.Over[R := R, ring := ring]` は環上の加群の自然数次数の余鎖複体を扱う。
各次数の台集合を `Family` の型値定義で返し、微分の線形性と二乗零を `Complex` にまとめる。
`Cohomology` は微分の核を境界の部分加群で割り、閉元の類・類の等式判定・完全元の零性と商の普遍性を公開する。
次数零の境界は零部分加群である。
余鎖写像はコホモロジー上の準同型へ降り、恒等写像と合成に整合する。

`Integer.Over[R := R, ring := ring]` は `std.Arithmetic.Int` の整数を次数に用いる。
各次数のコホモロジーは直前の微分の像を現在の微分の核の内部へ移した商である。
`Cochain.Over.ZeroExtension[C := C]` は非負次数で元の複体と同型、負次数で零空間となる整数次数の複体を構成する。
`Recovery` は非負次数への制限との往復とコホモロジー同型を、`BoundaryZero` と `BoundarySuccessor` は零次と正次数での境界の一致を公開する。
`PositiveCohomology[n].isomorphism` は整数次数 \(n\) の商と元の自然数次数 \(n\) の商を直接結ぶ。
`NegativeCohomology[n].isomorphism` は負次数 \(-n-1\) のコホモロジーと零空間の同型を返す。
`Integer.Over.Map` の誘導写像は、閉元と境界を保存することを証明して商へ降ろされ、恒等写像と合成に整合する。

一般の加群・核・像・商は `algebra.Module` を利用する。
実数上の具体化と、次数ごとに台集合が変わる利用例は [Cohomology.ref](../../tests/projects/manifolds-de-rham/src/Cohomology.ref) にある。

```sh
target/debug/cli libs/homological_algebra --no-cache --diagnostics compact
```
