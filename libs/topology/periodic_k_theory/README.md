# 周期的 K 理論

`periodic_k_theory` は、K08 の基本積定理から相対・被約 Bott 同型と整数次数の複素 K 理論を構成する。
相対群は閉対の商、負次数は被約 suspension、整数次数は偶奇による正規形を使う。
元の負次数との比較同型は `Integer.Comparison` が与える。

| API | 内容 |
| --- | --- |
| `Periodicity.beta` | 基点でランク零の K08 Bott 元 |
| `Reduced` / `Reduced.Inverse` | \(a\mapsto a\boxtimes\beta\) と逆写像、両側逆、加法性、零元 |
| `RelativePair` | 閉対の外積 \(K(X,A)\to K((X,A)\wedge(S^2,*))\) と両側逆 |
| `TwoShift` / `Negative` | \(\widetilde K^{-n}(X)\cong\widetilde K^{-(n+2)}(X)\) |
| `Integer.At` / `Absolute` / `Pair` | 全整数次数の群と2周期同型、引き戻し |
| `SixTerm` / `SixTerm.Naturality` | 閉対の6項完全列、6か所の完全性、6つの可換正方形 |
| `Product` | 整数次数の外積、双加法性、零元、負号、Koszul 指数の偶奇 |
| `SwapSphere` / `OddProduct` | suspension の2座標交換による Bott 元の負号と奇次数の積の符号 |
| `Point.At` / `Spheres.At` | 一点と被約球面群の整数次数での計算 |
| `BottSpheres` | 反復 Bott 外積による生成元、整数との同型、奇群の消滅 |

`Reduced.Naturality`、`TwoShift.Naturality`、`Negative.Naturality` は Bott 同型と引き戻しの可換性を公開する。
`RelativePair.Formula.productFormula` は、商を経由して作った相対同型が既存の相対外積と一致することを示す。

`SquareSphere` と `SuspensionSphere` は、正方形の境界を潰した空間から通常の \(S^2\) への具体的な基点付き同相を構成する。
`DoubleComparison` は、これを任意のコンパクト基点付き空間に対する \(\Sigma^2X\cong X\wedge S^2\) に移す。
座標交換の符号は、射影直線の束とその直交補空間を定数複素行列で比較して証明する。

一点の負一次群の消滅では、有限個の複素数を避ける折れ線から一般線形群の道連結性を証明する。
その経路で区間の両端の束同型を延長し、区間・境界対の相対群が零であることを示す。
この商を円周に同定することで、\(K^{-1}(*)=0\) と \(\widetilde K^0(S^1)=0\) を得る。

`Spheres.sphere n` は \(S^0\) の \(n\) 回の被約 suspension である。
計算は
\[
K^j(*)\cong
\begin{cases}\mathbb Z&j\equiv0\pmod2,\\0&j\equiv1\pmod2,\end{cases}
\qquad
\widetilde K^j(S^n)\cong
\begin{cases}\mathbb Z&j+n\equiv0\pmod2,\\0&j+n\equiv1\pmod2.\end{cases}
\]
`Coefficients.Carrier false` は全整数、`Coefficients.Carrier true` は零のみを許す整数の部分群である。
`Spheres.At.parityFormula` と `isomorphism` がこの表を型付きで与える。
`BottSpheres.comparison` は、反復 smash による偶数次元球面モデルと suspension モデルを同定する。
`iteratedBott` は各生成元が直前の生成元と Bott 元との外積であることを示し、`normalized` は整数座標が1であることを示す。

最小利用例は [Examples.ref](src/Periodicity/Examples.ref) と [Examples/Reduced.ref](src/Periodicity/Examples/Reduced.ref) にある。

```ref
\import periodic_k_theory.Periodicity[] \as K;
\import K.Point[] \as Point;
\definition pointMinusOne:
  \forall (x: Point.Odd) -> x = Point.oddGroup.base.unit := Point.oddZero;
```

通常検査はリポジトリルートで `cargo build -p cli --release --locked` と `python3 scripts/check_all.py` を実行する。
このパッケージの大きい比較図式には、必要に応じて `--memory-mib 8192` を指定する。
