# 一般5次方程式の根号非可解性

パッケージ名は `quintic`。
`galois` の体拡大・最小多項式・自己同型の延長・交換子列を使い、独立な5つの根から作る一般5次方程式の根号非可解性を証明する。

## 定理

代数的に閉じた定数体 \(C\) と、\(C\) 上代数的に独立な \(r_a,r_b,r_c,r_d,r_e\) を取る。
周囲の体 \(K\) は、\(C(r_a,r_b,r_c,r_d,r_e)\) 上代数的で、可算かつ代数的に閉じているものとする。
定数体内の自然数からの単射を与えて、部分体の無限性を表す。

\[
P(T)=\prod_{i\in\{a,b,c,d,e\}}(T-r_i)
     =T^5+a_4T^4+a_3T^3+a_2T^2+a_1T+a_0,
\qquad F=C(a_0,a_1,a_2,a_3,a_4).
\]

`Generic.Field.Over.Equation` は、この係数列と係数体 \(F\) を構成する。
`degree` は次数が5であること、`over` は全係数が \(F\) に属すること、`firstRoot` は \(P(r_a)=0\) を証明する。

`Generic.Field.Over.AbelRuffini` は次を証明する。

| 定理 | 結論 |
| --- | --- |
| `firstRootNotRadical` | \(r_a\) は \(F\) 上の根号閉包に属さない。 |
| `noRadicalFormula` | \(F\) の元、四則演算、有限回の根号から \(r_a\) を表す式は存在しない。 |
| `notSolvableByRadicals` | \(P\) は \(F\) 上根号で可解でない。 |
| `firstRootNotConstructible` / `noConstruction` | \(r_a\) は \(F\) 上の有限回の体演算と平方根では構成できない。 |
| `notConstructible` | 全根を \(F\) 上作図可能数で得ることはできない。 |

これらの定理は `Closure.Conditions` と定数体の代数的閉性を仮定とする含意である。
`Closure.Conditions` の内容は、\(K\) の代数的閉性、根の代数的独立性、定数体内の単射、\(K/C(r_a,r_b,r_c,r_d,r_e)\) の代数性である。
\(K\) の全元を尽くす列挙を module の引数として与える。
代数的独立性は、多変数多項式の評価の核が零であることで定義する。
`Distinctness.independentImpliesDistinct` が根の相異なることを導く。

## 証明の構成

1. 多変数多項式の変数の置換が環の関係を保つことを証明する。
2. 独立性から、多項式の分数による表示の関係が置換後も一致することを示し、\(C(r_a,r_b,r_c,r_d,r_e)\) の同型を構成する。
3. 最小多項式と単純拡大の同型を使い、可算な \(K\) の元を定義域と値域へ交互に加えて自己同型へ延長する。
4. 3つの具体的な置換について一次式の積を並べ替え、自己同型が \(P\) の係数を固定することを示す。
5. 根号で表せる元は交換子列のある段階で固定されることを使う。
   一方、\(c=(a\ b\ c)\) と具体的な \(s,t\) に対する \([scs^{-1},tct^{-1}]=c\) により、この3サイクルの作用はすべての段階で残る。
   \(r_a\ne r_b\) と矛盾する。

根の置換を延長できることも、根号による固定の性質も、結論として証明している。
利用する古典的選択は、既存の `classicalIndefiniteChoice` である。

## 使用する module

```text
\import quintic.Generic[].Field[K := K, field := field]
  .Over[constants := constants, roots := roots] \as Generic;
\import Generic.Equation[] \as Equation;
\import Generic.Closure[enumeration := enumeration, index := index] \as Closure;
\import Generic.AbelRuffini[enumeration := enumeration, index := index] \as AbelRuffini;
```

`K` は体の台集合、`field` は `std.Alg.Field.Field[K]`、`constants` は `galois.Field.Over.Subfield.Subfield`、`roots` は `galois.Quintic.Five -> K`。
`enumeration` は `std.Set.Countability[K].Enumerator`、`index` は `Nat -> K` である。
根号閉包と作図可能性の定義、有理数の代数閉包の定義は [galois](../galois/README.md) にある。

## 検査

リポジトリのルートから実行する。

```sh
cargo run -p cli -- libs/algebra/galois --module galois --full-check-local
cargo run -p cli -- libs/algebra/quintic --module quintic --full-check-local
```
