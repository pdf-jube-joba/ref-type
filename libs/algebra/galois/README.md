# 体拡大とガロア理論の基礎

部分体、体の埋め込み、自己同型、固定体、根号による生成、作図可能数を扱う。
パッケージ名は `galois`。

| module | 内容 |
| --- | --- |
| `Field.Over` | 任意の体の演算、非零元の逆数、零の逆数を零に正規化した演算。 |
| `Field.Over.Subfield` | 部分体、共通部分、生成部分体、単純添加、生成の最小性・単調性・冪等性。 |
| `Field.Over.Subfield.Of` | 部分体の台集合と体の法則。 |
| `Field.Over.Morphism` | 体準同型、単射性の証明、埋め込み、合成、べきの保存。 |
| `Field.Over.Automorphism` | 自己同型、逆、合成。 |
| `Field.Over.Correspondence` | 固定体、安定化群、ガロア群、反変なガロア接続、三重適用の恒等式。 |
| `Field.Over.Polynomial` | 係数列とモニック多項式、評価、既存の多項式環への変換、分解、代数性、根号可解性。 |
| `Field.Over.Generation` | 根号閉包と平方根閉包、部分体としての閉性、作図可能なら根号で表せること。 |
| `Field.Over.Generation.Construction` | 有限の体演算と平方根の式、式の妥当性、作図可能性との同値性。 |
| `Field.Over.Generation.RadicalExpression` | 有限の体演算と根号の式、根号閉包との同値性。 |
| `Permutation` | 置換、部分群、正規部分群、交換子部分群、交換子列、可解性、可換商による有限列。 |
| `Quintic` | 5点の具体的な置換による \(S_5\) の非可解性と、可換商を持つ有限の部分群列が存在しないこと。 |
| `RationalClosure` | 有理数の埋め込み、代数的数の集合、\(\mathbb Q\) の代数閉包の構造。 |
| `Examples.InField` | \(\sqrt2\) の作図可能性と有限の式、\(X^5-X-1\) の係数列。 |

## 使い方

```toml
[dependencies]
galois = { path = "../galois" }
```

```text
\import std.Alg[].Field[] \as Fields;
\module InField(K: \Set, field: Fields.Field[K]) {
  \import galois.Field[].Over[K := K, field := field].Generation[] \as Generation;
  \import galois.Field[].Over[K := K, field := field].Polynomial[] \as Polynomial;
}
\import galois.Quintic[] \as Quintic;
\import galois.RationalClosure[] \as Closure;
```

`Generation.Constructible S x` は、基礎集合 \(S\) を含み、体演算と平方根で閉じたすべての部分集合に \(x\) が属することをいう。
`Construction.characterization` は、この定義が有限の体演算と平方根の式による表示と同値であることを証明する。
`RadicalExpression.characterization` は、指数が2以上の根号について同じことを証明する。
実数体の部分体に適用すると、通常の実数の作図可能性の代数的な定義になる。

モニック多項式は、最高次の係数1を除いた低次からの係数列で表す。
空列は1、長さは次数であり、代数性の証人には正の次数を要求する。
最高次係数が1であるため、零多項式はこの表現に含まれない。
分解は `algebra.Polynomial.Over` の多項式環での一次式の積との等式で表す。
`SolvableByRadicals` は、指定した周囲の体における根号閉包内の分解と、全根が根号閉包に属することを要求する。

## \(S_5\) の非可解性

`Quintic.symmetricFiveNotSolvable` は、仮定を持たない \(\neg\operatorname{Solvable}(S_5)\) の証明である。
3サイクル \(c=(a\ b\ c)\) と2つの具体的な置換 \(s,t\) に対し、

\[
[scs^{-1},tct^{-1}]=c
\]

を5点それぞれで計算して証明する。
交換子部分群が共役で閉じることから、\(c\) は交換子列のすべての段階に残る。
\(c(a)\ne a\) なので、この列は単位部分群に到達しない。
`Permutation.Obstruction.persists` がこの議論の一般形である。

`Correspondence.galoisConnection` は固定体と安定化群の順序に関する接続を述べる。
`Quintic.symmetricFiveNotSolvable` が述べる対象は置換群であり、多項式の根号非可解性への翻訳には分解体と根号拡大に関する別の議論が必要になる。

## 有理数の代数閉包

`RationalClosure.AlgebraicClosureOfQ` は、台集合、体の構造、有理数の埋め込み、全元の \(\mathbb Q\) 上の代数性、代数的閉性を束ねる。
代数的閉性は、正の次数のすべてのモニック多項式に根が存在することで定義する。
`RationalClosure.In.AlgebraicNumbers` は、指定した周囲の体で有理数上代数的な元を取った refinement である。
代数閉包の構造を与えるには、代数性と代数的閉性の証明が必要になる。

## 検査

リポジトリのルートから実行する。

```sh
cargo run -p cli -- libs/algebra/galois --module galois
```
