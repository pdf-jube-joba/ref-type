# 抽象代数

`std.Alg` の構造を入力として、準同型、商、群完成、多項式環を構成する。
直接依存は `std` で、公開 module は [root.ref](src/root.ref) にある。

## 構成と定理

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
係数列による正規形、次数、体上の除法と互除法は次の実装単位となる。

## 型検査

リポジトリのルートで実行する。

```sh
target/debug/cli libs/algebra --no-cache --diagnostics compact
```

群完成の具体化には `GroupCompletion.Of[M := ..., monoid := ...]` を使う。
`Universal[K := ..., target := ...]` の `extension` と `unique` が、準同型の延長とその一意性を提供する。
型検査時に確認した言語上の制約と比較例は [gaps.md](../../_plans/gaps.md#g03) にある。
