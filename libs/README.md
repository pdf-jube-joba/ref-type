# 標準ライブラリ

各パッケージの `src/root.ref` は公開モジュールの一覧、`tests/projects/library/src/root.ref` は利用例を兼ねたライブラリ全体の型検査である。
現在の処理系には任意の証明を通す `admit` / `sorry` はない。処理系が持つ組み込み公理は、
必要な前提を検査する `\axiom:setext`、`\axiom:funext`、
`\axiom:classicalIndefiniteChoice` の3つである。集合の外延性、対応宣言の関数の外延性、古典論理の選択に、それぞれの公理を使う。

## モジュール構成

| 分野 | ファイル | 内容 |
| --- | --- | --- |
| 論理 | `Logic/Proposition.ref`、`Logic/Algebra/Def.ref`、`Logic/Rel.ref`、`Logic/Classical.ref`、`Logic/Equality.ref` | 命題、関係、法則、古典論理、等式 |
| データ | `Data/Bool.ref`、`Data/Pair.ref`、`Data/Sum.ref`、`Data/FinSet.ref` | 基本データ、直積、直和、有限集合 |
| 自然数 | `Data/Nat.ref`、`Data/Nat/Basic/`、`Data/Nat/Division/`、`Data/Nat/Gcd/` | 自然数の型、演算と仕様、法則 |
| 集合 | `Set/Quotient.ref` | 同値類、商の台集合、演算の relational image |
| 代数 | `Alg/Monoid.ref`、`Alg/Alg.ref`、`Alg/Ring.ref`、`Alg/Field.ref` | Monoid、Group、Semiring、Ring、Field、環上の加群、環上の代数 |
| 算術 | `Arithmetic/Int.ref`、`Arithmetic/Rat.ref`、`Arithmetic/IntAlgebra.ref` と各子モジュール | 整数、有理数、整数の代数構造 |
| 実数 | `real/src/AxiomaticReals.ref`、`real/src/DedekindReal.ref`、`real/src/CauchyReal.ref` と各子モジュール | 公理的実数、Dedekind 実数、Cauchy 実数 |
| 幾何 | `topology/src/root.ref` | 位相空間、実数値の距離空間と誘導位相 |

モジュールは関心ごとに階層を分け、定義は末端の `Def`、性質と証明は末端の `Prop` に置く。
例えば `std/src/Data/Nat/Division.ref` の `\module Def;` の本体は `std/src/Data/Nat/Division/Def.ref` にある。
子ファイルは親のスコープを引き継ぐので、同じ依存を改めて import して型の instance を作り直さない。

## 選言の場合分け

`either!` は左右の証明から結論を導く関数を受け取り、`Logic.Or[P, Q] -> R` を構成する。

```text
\import std.Logic[].Proposition[] \as Logic;
\use Logic.either;

either!{
  P "or" Q "either" R
  "lt:" {\fun (p: P) => fromLeft p}
  "rt:" {\fun (q: Q) => fromRight q}
} disjunction
```

## 等式と合同則

等式の基本操作は carrier をマクロ引数にして使用する。

```text
\import std.Logic[].Equality[] \as Equality;
\use Equality.sym;
\use Equality.trans;
\use Equality.congr;
\use Equality.congr2;

trans!{A} a b c ab bc
congr!{A B} f a b ab
congr2!{A B C} f a b c d ab cd
```

等式を順につなぐには `eq_reason!` を使う。
各 `"by"` の証明は直前の段から次の段への等式であり、全体は始点から終点への等式になる。

```text
\use Equality.eq_reason;

\definition chained: a = c := eq_reason!{
  a "=" b "by" ab
    "=" c "by" bc
};
\definition mapped: f a = f c := eq_reason!{
  { f a } "=" { f b } "by" { congr!{A B} f a b ab }
          "=" { f c } "by" { congr!{A B} f b c bc }
};
```

`eq_reason!{a}` は反射律による `a = a` の証明になる。

自然数と整数には、加法・乗法を表す数式マクロがある。
各例は、それぞれの数の記法を使うモジュール内に置く。

```text
\import std.Data[].Nat[] \as N;
\import std.Data[].Nat[].Basic[].Def[] \as NatOp;
\import std.Data[].Nat[].Basic[].Prop[] \as NL;
\use NatOp.nat_add;
\use NatOp.nat_mul;

\definition distribute (a, b, c: N.Nat^):
  \(a "*" (b "+" c)\) = \((a "*" b) "+" (a "*" c)\) :=
  NL.mulDistribLeft a b c;
```

```text
\import std.Arithmetic[].Int[] \as I;
\import std.Logic[].Equality[] \as E;
\use I.int_add;
\use I.int_mul;
\use E.eq_reason;

\definition expanded (a, b, c: I.Integer):
  \(a "*" (b "+" c)\) = \((b "*" a) "+" (c "*" a)\) :=
  eq_reason!{
    \(a "*" (b "+" c)\)
    "=" \((b "+" c) "*" a\) "by" { I.mulIntegerComm a \(b "+" c\) }
    "=" \((b "*" a) "+" (c "*" a)\) "by" { I.mulIntegerDistribRight b c a }
  };
```

自然数の記法は `Add::[set]`・`Mul::[set]`、整数の記法は `addInteger`・`mulInteger` に展開される。

`congr2!` は `ab: a = b` と `cd: c = d` から `f a c = f b d` を直接作る。
期待型から引数が分かる場合は値を `_` にできる。

```text
congr2!{Nat^ Nat^ Nat^} natAdd _ _ _ _ leftEq rightEq
```

したがって、単に二引数関数へ等式を写すだけのローカル補題は通常不要である。
`Nat.addCong` のような型固有の名前は公開 API として残すが、数の証明内部では
`congr!` / `congr2!` / `congr3!` を直接使える。

固定した carrier の名前付き API が必要なら、次の形も使える。

```text
\import std.Logic[].Equality[].Prop[A := X] \as E;
```

現在の PTS では命題内で `Set` 自体を量化しないため、carrier はマクロ展開時に指定する。
また module import は生成的であり、import ごとに別の型 instance を作る。
同じモジュールで宣言した型に対しては、補助モジュールを再 import するより、
使用箇所で等式マクロを具体化する方が安全である。

## 代数構造

代数構造は `\structure` でデータと法則をまとめて宣言する。
`Monoid[A]::[Raw]` は単位元と演算、`Monoid[A]::[Law][s]` はその法則、`Monoid[A]::[Set]` は法則を満たす構造の型である。
構造の要素からは `#op{s}` と `#leftIdentity{s}` のようにデータと法則を直接取り出せる。

`Alg.Monoid`、`Alg.Alg`、`Alg.Ring`、`Alg.Field` は次の構造を提供する。

- `Monoid` / `CommutativeMonoid`
- `Group` / `CommutativeGroup`
- `Semiring`
- `Ring` / `CommutativeRing`
- `Field`
- `RingModule[Scalars, Carrier, r]` / `RingAlgebra[Scalars, Carrier, r]`

可換版は基礎構造の Raw データを `base` field に持ち、基礎構造の法則と可換律をまとめる。
`asMonoid`、`asGroup`、`commutativeRingAsRing` はそのデータと法則から基礎構造を構成する。
加法・乗法部分も、それぞれの構造の law を再利用する。
[利用例](../tests/projects/library/src/root.ref)には Nat の加法モノイドと半環の構成がある。
`IntAlgebra` は `Int` の加法について、左右単位元・結合則・左右逆元・可換律をまとめた `CommutativeGroup` を公開する。
この接続は整数本体とは別モジュールに置き、`Int` と代数構造の依存順を保っている。

## 直積と有限部分集合

`Pair.Times(A, B: \VType): \VType` が Program の対を定義し、その Set 表現
`Pair.Times^[A, B]` も生成する。Set 側では次を使う。

- `pair A B a b`、`first A B p`、`second A B p`
- `swap A B p`
- `map A B C D f g p`
- `mapFirst A B C f p`、`mapSecond A B C g p`（片側だけを写す）
- `curry A B C f`、`uncurry A B C f`
- `assoc A B C p`（`((a,b),c)` から `(a,(b,c))`）、`unassoc A B C p`（逆方向）

Set の carrier は Program 表現を持たなくてもよい。型引数を推論できる場合は `_` にできる。
`P.Prop[A := A, B := B]` は `induction`、`eta`、`ext`、`pairCong`、射影の合同則、
`pairInjectiveFirst` / `pairInjectiveSecond` を公開する。
`P.Mapping[A := A, B := B, C := C, D := D].Prop[]` には写像の計算則・合成則・
片側の写像と両側の写像の一致があり、`P.Functions[A := A, B := B, C := C].Prop[]` には
カリー化と結合の組み替えが互いに逆になる法則がある。

Program では `P.Times[A, B]::pair a b` が値を構築する。型引数は `[_, _]` と書いて推論させられる。
`P.Times::make a b`、`P.Times::first p`、`P.Times::second p`、`P.Times::swap p` は計算であり、
型引数を省略できる。型を固定して複数の操作を使う場合は、同じ Pair instance の子を開く。

```text
\import std.Data[].Pair[] \as P;
\import P.Program[A := A, B := B] \as PP;
\import PP.Def[] \as PD;
\import PP.Mapping[C := C, D := D].Def[] \as PM;
\import PP.Functions[C := C].Def[] \as PF;
```

ここで `A`、`B`、`C`、`D` は Program の値型である。

| モジュール | 操作 | 引数と結果 |
| --- | --- | --- |
| `PD` | `Make::[program] a b`、`First::[program] p`、`Second::[program] p`、`Swap::[program] p` | 型関連操作と同じ |
| `PM` | `Map::[program] f g p` | `f: \U(A ~> \F(C))`、`g: \U(B ~> \F(D))` で両成分を写す |
| `PM` | `MapFirst::[program] f p`、`MapSecond::[program] g p` | 片側だけを写し、もう一方の値を保持する |
| `PF` | `Curry::[program] f a b` | `f: \U(P.Times[A, B] ~> \F(C))` を呼ぶ |
| `PF` | `Uncurry::[program] f p` | `f: \U(A ~> B ~> \F(C))` を呼ぶ |
| `PF` | `Assoc::[program] p`、`Unassoc::[program] p` | 三成分の結合を組み替える |

各操作は `\correspondence` で宣言し、`::[set]` は任意の Set を扱う親モジュールの演算を具体化する。
`::[coherence]` は任意の反映された引数について Program 演算と Set 演算の一致を示す。

`map` は左、右の順に各関数を1回ずつ実行する。関数は `\thunk f` の形で渡し、
計算結果は `\bind` で受け取る。複数引数の計算は `Make::[program] a b` のように直接適用する。

```text
\definition transform(p: P.Times[A, B]): \F(C) := \program {
  \bind mapped: P.Times[C, D] <- PM.Map::[program] (\thunk f) (\thunk g) p \then
  \bind result: C <- P.Times::first mapped \then
  \return result
};
```

`f: A ~> \F(C)`、`g: B ~> \F(D)` はあらかじめ定義した計算とする。
停止性が確認できる計算は通常どおり `\box` / `\Force` で Set に反映できる。
[利用例](../tests/projects/library/src/root.ref)の `PairExamples` は全操作の反映と Set の仕様の一致を証明し、
Bool と Nat を使った直接の Program 呼び出しも検査する。

`NatPair` と Int の `Difference` はこの対型の alias である。Rat の `Integer` は
Int の正規形キャリアを使い、形式差との往復は `Int.Math` が担う。

`Set.FiniteSubset(A := A)` は、空集合と有限回の `insert` で生成される `Power(A)` の
subtype を提供する。`empty`、`insert`、`singleton`、`unorderedPair` で有限部分集合を
構築し、`Member` で所属、`induction` で有限集合についての帰納法を表す。大文字の
`Empty`、`Insert`、`Singleton`、`UnorderedPair` は対応する生の `Power(A)` である。
`unorderedPair a b` は `{a, b}` であり、`a = b` の場合は一点集合になるため、濃度が
常に2であることは主張しない。

## 商への演算の持ち上げ

`Quotient` は、同値関係を保つ単項・二項演算のために `UnaryRespects` / `BinaryRespects`、
`UnaryImage` / `BinaryImage` を提供する。`induction` は商についての命題を代表元の場合へ帰着する。
`unaryImageClass` / `binaryImageClass` は代表元上の
image が期待する同値類に一致することを示し、`unaryImageClosed` / `binaryImageClosed` は
image が再び商の要素になることを示す。演算ごとに同じ外延性証明を作り直す必要はない。

## Program 演算と仕様

Bool・Nat・Int は `\VType` の Program データであり、Set 側の型は `Bool^`・`Nat^`・`Int^`。
反映後の constructor は `Bool^::true`、`Nat^::succ` のように参照する。
Bool・Nat・Int の演算は `\correspondence` で実装・仕様・一致証明をまとめて宣言する。

| member | 用途 |
| --- | --- |
| `Add::[program]` | Program の加算 |
| `Add::[set]` | Set の加算仕様 |
| `Add::[coherence]` | 実装の反映と仕様の等式 |

算術法則と数学側の構成は `::[set]` を使い、実行結果との接続には `::[coherence]` を使う。
`AddLoop::[run]` や `IterLoop::[run]` は、状態遷移と停止性証明をまとめた `\machine` の実行関数である。
反復の構造は `Data.Nat.Iteration`、実装は `Iteration.Def[A := A]`、不変条件の保存は `Iteration.Prop[A := A]` にまとめる。
Bool は `Neg`、`And`、`Or`、`Xor`、`Implies`、`Eqb`、Int は `Diff`、`Neg`、`Add`、`Mul` などの対応宣言を公開する。
Int の `Zero`、`One`、`MinusOne` も同じ member で定数の実装・仕様・一致証明を提供し、差分の計算は `DiffLoop::[run]` にまとめている。

`\run` は部分計算を表せるが、Set に反映する際には停止性証明が必要になる。

自然数の型は `Data.Nat` にあり、加減乗算、累乗、比較は `Data.Nat.Basic.Def`、除算と剰余は `Data.Nat.Division.Def`、有限反復は `Data.Nat.Iteration.Def`、偶奇判定は `Data.Nat.Parity.Def`、最大公約数は `Data.Nat.Gcd.Def` にある。
除数が零なら `div a 0 = 0`、`mod a 0 = a` とし、`0^0 = 1` とする。
自然数は単項表現なので、大きな具体値の評価には向かない。

偶奇判定の Set 側は剰余 2 がそれぞれ零・一であることを判定する。
GCD の Set 側は、共通約数であり、すべての共通約数で割り切れる自然数を、一意存在の証明付き `\choice` で取り出す。
Program 側のユークリッド互除法は、この性質を満たすことから Set 側と一致する。

一般の算術法則は `Data.Nat.Basic.Prop`、除算・剰余・整除の法則と GCD の存在・一意性は `Data.Nat.Division.Prop`、数学的な GCD の法則は `Data.Nat.Gcd.Prop` にある。

```text
\import std.Data[].Nat[] \as N;
\import std.Data[].Nat[].Basic[].Def[] \as NatOp;
\import std.Data[].Nat[].Basic[].Prop[] \as NL;
\import std.Data[].Nat[].Division[].Prop[] \as ND;
\import std.Data[].Nat[].Gcd[].Def[] \as G;
\import std.Data[].Nat[].Gcd[].Prop[] \as GL;
```

Int は `ofNat n` と `negSucc n` からなる一意な Program 正規形を持つ。
数学側では自然数対 `(a,b)` を `a+d=c+b` で同一視した群完成 `Grothendieck` を構成し、
`toMath` / `fromMath` と `*MatchesMath` が Program 演算との対応を与える。
加法の結合則と乗法の可換律も、この対応を通して具体的な `Int` 上へ戻してある。
整数の除算・剰余・GCD は未実装である。

群完成とその上の演算は `Int.Math`、Program 仕様との対応は
`Int.Math.Specification.Def`、代数法則は `Int.Math.Specification.Prop` に分離している。

```text
\import std.Arithmetic[].Int[] \as I;
\import I.Math[] \as IM;
\import IM.Specification[] \as Specification;
\import Specification.Def[] \as IS;
\import Specification.Prop[] \as IL;
```

Program の逐次計算は `\program` 内の `\bind` 文で記述する。各 block は最後に
`\return value` を置き、中間文は `\then` でつなぐ。旧来の深く入れ子になった `\bind ... \in ...` は使わない。

別々に import した Nat / Bool の instance は混ぜられない。Int と組み合わせる場合は、
Int が公開する `Nat` / `Bool` alias と `natZero!{}`、`natSucc!{n}`、
`boolTrue!{}`、`boolFalse!{}` を使う。

## 有理数

Rat の分子 `Integer` は Int の `ofNat` / `negSucc` 正規形であり、その法則と合同則は組み込みの `=` を使う。
形式差 `Difference` 上の `Equivalent` は代表元の関係を表し、`normalizeRespects` で正規形の等式へ移す。

`Fraction` は分子と `denominatorIndex` を保持する。index `d` は実際の分母 `d+1` を表すため、
零分母は構文的に作れない。`FractionEq` は交差積による同値関係である。
推移律 `fractionEqTrans` では `Nat.mulCancelRightSucc` を使い、中央の正の分母を消去する。

`Rat` は Int による整数演算、`Rat.Fractions` は正分母の分数代表、
`Rat.Fractions.Arithmetic` は分数演算、
`Rat.Fractions.Quotient` は商構成を担当する。

```text
\import std.Arithmetic[].Rat[] \as R;
\import R.Fractions[] \as RF;
\import RF.Arithmetic[].Def[] \as RO;
\import RF.Quotient[] \as RQ;
```

`Rat.Fractions.Arithmetic.Def` は分数の演算、`Rat.Fractions.Arithmetic.Prop` は同値関係の保存と算術法則を公開する。
`Rat.Fractions.Quotient` は証明済みの `FractionEq` を汎用 `Quotient` に渡し、商上の加法、反数、乗法とその法則を構成する。
`Rat.Fractions.Quotient.Arithmetic.Def` は商上の加法・減法・乗法の操作をまとめる。
`Rat.Fractions.Quotient.Division.Def` は除法の image が同値類になる証明を受け取り、商上の除法を構成する。

## 実数

Dedekind 実数は inhabited・proper・lower・rounded・located な切断として定義される。
`DedekindReal.Cuts.Def` は切断の候補となる lower set、`Cuts.Prop` はそれらが切断になる証明を公開する。
`DedekindReal.Arithmetic.Def` は切断上の演算、`Arithmetic.Prop` は算術法則を公開する。
`DedekindReal.Field.Def` は演算と法則を公理的実数の構造へまとめる。

Cauchy 実数は有理数列を「差が零へ収束する」関係で割った商である。
`CauchyReal.Quotient.Sequences.Def` は列上の演算、`Classes.Def` は同値類上の演算を構成する。
`CauchyReal.Quotient.Arithmetic.Def` と `Arithmetic.Prop` は商上の算術、`Inverse.Def` と `Inverse.Prop` は逆数の構成と性質を公開する。
順序と完備性はそれぞれ `CauchyReal.Order` と `CauchyReal.Completeness` にある。

## 型検査

```sh
cargo run --quiet -- libs/std
cargo run --quiet -- tests/projects/library
cargo test --workspace
```

最初の2つはライブラリ定義と公開 API の利用例を型検査する。最後のコマンドは、
処理系の unit test、`.ref` の成功・失敗テスト、doc test をすべて実行する。
