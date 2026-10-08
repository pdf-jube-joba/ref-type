# 標準ライブラリ

`std` は他のパッケージに依存せず、論理・データ・集合・算術・代数構造を提供する。
公開 module は [root.ref](src/root.ref)、利用例は [library project](../../tests/projects/library/src/root.ref) を参照。

| module | 内容 |
| --- | --- |
| [Logic](src/Logic.ref) | 命題、等式、古典論理、関係、順序、停止性 |
| [Data](src/Data.ref) | Bool、Nat、Pair、List、Option、Sum、有限集合 |
| [Set](src/Set.ref) | 商と有限部分集合 |
| [Arithmetic](src/Arithmetic.ref) | 整数、有理数 |
| [Alg](src/Alg.ref) | モノイド、群、環、体、加群、代数 |
| [Program](src/Program.ref) | 実装と仕様の対応、停止性を持つ状態遷移 |

## 等式と合同則

carrier をマクロ引数に指定して使う。

```text
\import std.Logic[].Equality[] \as E;
\use E.trans;
\use E.congr;
\use E.congr2;
\use E.eq_reason;

trans!{A} a b c ab bc
congr!{A B} f a b ab
congr2!{A B C} f a b c d ab cd

eq_reason!{a "=" b "by" ab "=" c "by" bc}
eq_reason!{{ f a } "=" { f b } "by" { congr!{A B} f a b ab }}
```

固定した carrier の名前付き API は `E.Prop[A := X]` にある。
選言の消去には `Logic.Proposition.either` を使える。

## Program と算術

Bool・Nat・Int は Program のデータで、反映した型は `Bool^`・`Nat^`・`Int^` である。
Bool と Int の演算は `Program.Correspondence` の `program`・`specification`・`coherence` で実装、Set の仕様、一致証明をまとめる。
Nat の演算は数学的な関数を `Def`、計算実装を `Program`、両者の対応を `ProgramProp` から参照する。
反復計算は `Program.Machine` の `step`・`terminates`・`run` で扱う。

| module | 内容 |
| --- | --- |
| `Data.Nat.Basic` | 加減乗算、累乗、比較 |
| `Data.Nat.Division` | 除算、剰余、整除の法則 |
| `Data.Nat.Iteration` / `Parity` / `Gcd` | 有限反復、偶奇判定、最大公約数 |
| `Arithmetic.Int.Math` | 自然数対の形式差と群完成 |
| `Int.Math.Specification` | 正規形の整数と群完成の対応・法則 |
| `Arithmetic.IntAlgebra` | 整数の加法可換群 |
| `Arithmetic.Rat.Fractions` | 正分母の分数と交差積による同値関係 |
| `Rat.Fractions.Quotient` | 商上の四則演算と代表元上の計算との一致 |

Nat の各演算 module は、`Def` に Set 上の数学的な定義、`Prop` にその法則を置く。
計算実装と停止性は `Program`、数学的な関数との一致証明と `Correspondence` は `ProgramProp` に置く。
例えば `Data.Nat.Basic.Def.add` が数学的な加算、`Data.Nat.Basic.Program.add` が計算用の thunk、`Data.Nat.Basic.ProgramProp.Add.coherence` が両者の一致証明である。
汎用の Set 上の反復は `Data.Nat.Iteration.Def` にある。
自然数では `div a 0 = 0`、`mod a 0 = a`、`0^0 = 1` とする。
単項表現なので大きな具体値の評価には向かない。
Int は `ofNat n` / `negSucc n` の正規形を持ち、`toMath` / `fromMath` が群完成と対応する。
分数の `denominatorIndex d` は分母 `d+1` を表す。

## 対と集合

`Data.Pair.Times[A, B]` は Program の対、`Times^[A, B]` は任意の Set を carrier に取れる反映型である。
Set 側は `pair`、`first`、`second`、`swap`、`map`、`curry`、`uncurry`、`assoc`、`unassoc` を使う。
Program 側の型関連操作は計算を返すので、結果を `\bind` で受け取る。

```text
\import std.Data[].Pair[] \as P;
\definition swap(A, B: \VType)(p: P.Times[A, B]): \F(P.Times[B, A]) :=
  \program {
    \bind a: A <- P.Times::first p \then
    \bind b: B <- P.Times::second p \then
    \return P.Times[B, A]::pair b a
  };
```

`Pair.Program` の `Def`・`Mapping.Def`・`Functions.Def` は対応宣言として同じ操作を提供する。
[FiniteSubset](src/Set/FiniteSubset.ref) は空集合と有限回の `insert` で生成される部分集合型である。
`Data.FinSet` は要素の列挙と網羅性、`Fin(n+1)` と `Option[Fin(n)]` の往復を提供する。
`Data.FinSet.Permutations` は有限集合上の全単射と交換の列を定義し、`PermutationDecomposition.decomposition` は任意の全単射が交換の列で表せることを証明する。
`Data.FinSet.Scope.finiteWhole` は列挙から有限性を示し、`Set.FiniteSubset.Enumeration.finiteOfEnumeration` は一般の有限リストから集合の有限性を導く。

## 商と代数構造

[Quotient](src/Set/Quotient.ref) は同値類と代表元、商の帰納法、単項・二項演算の持ち上げを提供する。
同値関係の法則は `EquivalenceLaws` として定理の前提で量化する。
[Logic.Rel](src/Logic/Rel.ref) は carrier と関係をまとめた `RelationData` / `EquivalenceRelation`、[QuotientOf](src/Logic/Rel/QuotientOf.ref) はその商を束として扱う。

代数構造はデータと法則を `\structure` にまとめる。
`Alg.Monoid`、`Alg.Alg`、`Alg.Ring`、`Alg.Field` が Monoid・Group・Semiring・Ring・Field と可換版を提供する。
`RingModule` / `RingAlgebra` はスカラー環と carrier を指定する。
利用例では自然数の加法モノイド・半環と整数の加法可換群を検査する。
