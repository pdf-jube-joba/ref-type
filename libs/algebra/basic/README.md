# 抽象代数

準同型、群完成、商、多項式環を扱う。

| module | 公開する内容 |
| --- | --- |
| `Hom` | モノイド・群・半環・環の準同型とモノイド準同型の合成。 |
| `Quotient` | 同値関係による商、演算の降下、代表元によらない写像の一意な延長。 |
| `Quotient.Groups` / `Quotient.Rings` | 合同関係による可換群・可換環の商構造。 |
| `Group.Of.Subgroups` | 零元・和・逆元で閉じた部分集合上の可換群。 |
| `GroupCompletion.Of` | 一般の可換モノイドの群完成と、可換群への準同型の一意な延長。 |
| `GroupCompletion.Natural` | 自然数の加法モノイドの群完成と既存の整数との同型、加法の保存。 |
| `GroupCompletion.Semiring` | 半環の群完成の環構造、半環準同型の環準同型への一意な延長、積の可換性の保存。 |
| `Exact` | 核・像・完全性、完全性から合成が零になること、可換群準同型の核・像の群構造。 |
| `FreeCommutativeRing.Over.Presentation` | 係数環と変数・関係から作る可換環の表示と普遍性。 |
| `FreeAssociativeRing.Over.Presentation` | 中心的な係数を持つ非可換な結合環の表示、結合代数構造と普遍性。 |
| `Groups.On` | 一般の群の逆元・共役、部分群、生成部分群、直積、中心的な符号元による商。 |
| `Groups.Units` | 環の可逆元群、逆元の一意性と可逆元の外延性。 |
| `Polynomial.Over` | 一変数多項式環、係数写像と変数の値で定まる評価準同型とその一意性。 |
| `LaurentPolynomial.Over` | Laurent 多項式環、可逆元への評価準同型とその一意性。 |

可換モノイドの群完成は、形式差の関係

\[
(a,b)\sim(c,d)\quad\Longleftrightarrow\quad\exists e,\quad a+d+e=c+b+e
\]

で定義する。
この関係の同値性、演算との整合性、群の法則、普遍性を証明している。
半環の積は加法に関する普遍性を二度使って延長する。

多項式環と Laurent 多項式環は、式の集合を最小の環合同関係で割って構成する。
`FreeCommutativeRing` の表示は追加の関係を持つ係数環上の可換環にも利用できる。
体上の係数列のモニック化とモニック除法は `galois.Field.Over.Polynomial.Raw`、一般の非零除数への除法・互除法と Bézout 係数は [polynomial_linear_algebra](../polynomial_linear_algebra/README.md) を参照。

`Noncommutative` は一般の群、部分群、右作用、安定化部分群、左剰余類の右作用を扱う。
`Actions.At` は、推移的な右作用と選んだ点の安定化部分群の剰余類作用の間の同変全単射を構成する。

`AmalgamatedProduct` は群の融合積の普遍性と、普遍性を満たす二つの群の標準同型を提供する。
`Noncommutative.Actions.PointedMaps` は推移的な群作用間の基点付き同変写像を安定化部分群の包含から構成する。
`GroupTransport` は相互逆な全単射で群構造を移す。
