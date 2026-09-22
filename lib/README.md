# 標準ライブラリ

`root.ref` は公開モジュールの一覧、`tests.ref` は利用例を兼ねたライブラリ全体の型検査である。
現在の処理系には任意の証明を通す `admit` / `sorry` はない。処理系が持つ組み込み公理は、
必要な前提を検査する `\axiom:setext`、`\axiom:funext`、
`\axiom:classicalIndefiniteChoice` の3つである。現在の `lib/` が実際に使うのは `setext` だけである。

## モジュール構成

| 分野 | ファイル | 内容 |
| --- | --- | --- |
| 論理 | `Logic/Proposition.ref`、`Logic/Law.ref`、`Logic/Rel.ref`、`Logic/Classical.ref`、`Logic/Equality.ref` | 命題、関係、法則、古典論理、等式 |
| データ | `Data/Bool.ref`、`Data/Pair.ref`、`Data/Sum.ref`、`Data/FinSet.ref` | 基本データ、直積、直和、有限集合 |
| 自然数 | `Nat.ref` と `Nat/` 以下 | 自然数の演算、仕様、法則 |
| 集合 | `Set/Quotient.ref` | 同値類、商の台集合、演算の relational image |
| 代数 | `Algebra/Monoid.ref`、`Algebra/Algebra.ref` | Monoid、Group、Semiring、Ring、Field |
| 算術 | `Arithmetic/Int.ref`、`Arithmetic/Rat.ref`、`Arithmetic/IntAlgebra.ref` と各子モジュール | 整数、有理数、整数の代数構造 |
| 実数 | `Reals/AxiomaticReals.ref`、`Reals/DedekindReal.ref`、`Reals/CauchyReal.ref` と各子モジュール | 公理的実数、Dedekind 実数、Cauchy 実数 |
| 幾何 | `Geometry/Topology.ref` | 位相空間 |

入れ子モジュールは論理上のパスと同じ場所に置く。例えば
`Arithmetic/Rat/Fractions/Operations.ref` の `\module Quotient;` の本体は
`Arithmetic/Rat/Fractions/Operations/Quotient.ref` にある。子ファイルは親のスコープを引き継ぐので、
同じ依存を改めて import して型の instance を作り直さない。

## 等式と合同則

等式の基本操作は carrier をマクロ引数にして使用する。

```text
\import \root.Logic[].Equality[] \as Equality;
\use Equality.sym;
\use Equality.trans;
\use Equality.congr;
\use Equality.congr2;

trans!{A} a b c ab bc
congr!{A B} f a b ab
congr2!{A B C} f a b c d ab cd
```

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
\import \root.Logic[].Equality[].Laws[A := X] \as E;
```

現在の PTS では命題内で `Set` 自体を量化しないため、carrier はマクロ展開時に指定する。
また module import は生成的であり、import ごとに別の型 instance を作る。
同じモジュールで宣言した型に対しては、補助モジュールを再 import するより、
使用箇所で等式マクロを具体化する方が安全である。

## 代数構造

`Monoid[]` は carrier を module parameter に持たず、`RawMonoid[A]` と
`MonoidLaws[A, s]` を分離し、両者を満たす値を `Monoid A` として表す。
`CommutativeMonoid` も同じ raw data を使う。
`monoidLawsIntro` と `commutativeMonoidLawsIntro` は法則レコードの構築を補助する。

`Algebra[]` は carrier を各 record の parameter として受け取り、次の構造を提供する。

- `Group` / `CommutativeGroup`
- `Semiring`
- `Ring` / `CommutativeRing`
- `Field`

ここでも `RawSemiring` のような Set-valued data、`SemiringLaws` のような Prop-valued laws、
その refinement を分ける。加法・乗法部分は `Monoid` の法則を再利用する。
`tests.ref` では Nat の加法モノイドと半環を具体的に構成している。
`IntAlgebra` は `Int` の加法について、左右単位元・結合則・左右逆元・可換律をまとめた
`CommutativeGroup` を公開する。`Int` が `Algebra` より先にロードされる依存順を保つため、
この接続は整数本体とは別モジュールに置いている。

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
`P.Laws(A := A, B := B)` は `induction`、`eta`、`ext`、`pairCong`、射影の合同則、
`pairInjectiveFirst` / `pairInjectiveSecond` を公開する。
`P.MapLaws(A := A, B := B, C := C, D := D)` には写像の計算則・合成則・
片側の写像と両側の写像の一致があり、`P.FunctionLaws(A := A, B := B, C := C)` には
カリー化と結合の組み替えが互いに逆になる法則がある。

Program では `P.Times[A, B]::pair a b` が値を構築する。型引数は `[_, _]` と書いて推論させられる。
`P.Times::make a b`、`P.Times::first p`、`P.Times::second p`、`P.Times::swap p` は計算であり、
型引数を省略できる。型を固定して複数の操作を使う場合は、同じ Pair instance の子を開く。

```text
\import \root.Data[].Pair[] \as P;
\import P.Program[A := A, B := B] \as PP;
\import PP.Mapping[C := C, D := D] \as PM;
\import PP.Functions[C := C] \as PF;
```

ここで `A`、`B`、`C`、`D` は Program の値型である。

| モジュール | 操作 | 引数と結果 |
| --- | --- | --- |
| `PP` | `make a b`、`first p`、`second p`、`swap p` | 型関連操作と同じ |
| `PM` | `map f g p` | `f: \U(A ~> \F(C))`、`g: \U(B ~> \F(D))` で両成分を写す |
| `PM` | `mapFirst f p`、`mapSecond g p` | 片側だけを写し、もう一方の値を保持する |
| `PF` | `curry f a b` | `f: \U(P.Times[A, B] ~> \F(C))` を呼ぶ |
| `PF` | `uncurry f p` | `f: \U(A ~> B ~> \F(C))` を呼ぶ |
| `PF` | `assoc p`、`unassoc p` | 三成分の結合を組み替える |

`map` は左、右の順に各関数を1回ずつ実行する。関数は `\thunk f` の形で渡し、
計算結果は `\bind` で受け取る。複数引数の計算は `make a b` のように直接適用する。

```text
\definition transform(p: P.Times[A, B]): \F(C) := \program {
  \bind mapped: P.Times[C, D] <- PM.map (\thunk f) (\thunk g) p \then
  \bind result: C <- P.Times::first mapped \then
  \return result
};
```

`f: A ~> \F(C)`、`g: B ~> \F(D)` はあらかじめ定義した計算とする。
停止性が確認できる計算は通常どおり `\box` / `\Force` で Set に反映できる。
`tests.ref` の `PairExamples` は全操作の反映と Set の仕様の一致を証明し、
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
各演算には原則として次の層がある。

- `add`: Program 演算
- `addSet`: `\box` / `\Force` による Set への反映
- `addPrec`: primitive recursor による仕様
- `addMatchesPrec`: 反映した演算と仕様の一致

`\run` は部分計算を表せるが、Set に反映する際には停止性証明が必要になる。

Nat は加減乗除、累乗、比較、有限反復、偶奇、GCD を持つ。除数が零なら
`div a 0 = 0`、`mod a 0 = a` とし、`0^0 = 1` とする。自然数は単項表現なので、
大きな具体値の評価には向かない。

Program 演算とその直接の仕様は `Nat` 本体に置き、一般の算術法則は `Nat.Laws`、
除算・剰余・GCD の再構成則・剰余の上界・最大公約数の法則は
`Nat.Laws.Division` に分離している。親と同じ Nat instance を使うには、次のように
import 済み instance から child を順に開く。

```text
\import \root.Nat[] \as N;
\import N.Laws[] \as NL;
\import NL.Division[] \as ND;
```

Int は `ofNat n` と `negSucc n` からなる一意な Program 正規形を持つ。
数学側では自然数対 `(a,b)` を `a+d=c+b` で同一視した群完成 `Grothendieck` を構成し、
`toMath` / `fromMath` と `*MatchesMath` が Program 演算との対応を与える。
加法の結合則と乗法の可換律も、この対応を通して具体的な `Int` 上へ戻してある。
整数の除算・剰余・GCD は未実装である。

群完成とその上の演算は `Int.Math`、Program 仕様との対応は
`Int.Math.Specification`、代数法則は `Int.Math.Specification.Laws` に分離している。

```text
\import \root.Arithmetic[].Int[] \as I;
\import I.Math[] \as IM;
\import IM.Specification[] \as IS;
\import IS.Laws[] \as IL;
```

Program の逐次計算は `\program` 内の `\bind` 文で記述する。各 block は最後に
`\return value` を置き、中間文は `\then` でつなぐ。旧来の深く入れ子になった `\bind ... \in ...` は使わない。

別々に import した Nat / Bool の instance は混ぜられない。Int と組み合わせる場合は、
Int が公開する `Nat` / `Bool` alias と `natZero!{}`、`natSucc!{n}`、
`boolTrue!{}`、`boolFalse!{}` を使う。

## 有理数

Rat の分子 `Integer` は Int の `ofNat` / `negSucc` 正規形である。`IntegerEq` は
正規形を `Int.Math` の形式差へ写して得る同値関係であり、
`addIntegerRespects`、`negIntegerRespects`、`subIntegerRespects`、
`mulIntegerRespects` が各演算の代表元独立性を与える。

`Fraction` は分子と `denominatorIndex` を保持する。index `d` は実際の分母 `d+1` を表すため、
零分母は構文的に作れない。`FractionEq` は交差積による同値関係である。
推移律 `fractionEqTrans` では `Nat.mulCancelRightSucc` を使い、中央の正の分母を消去する。

`Rat` は Int による整数演算、`Rat.Fractions` は正分母の分数代表、
`Rat.Fractions.Operations` は分数演算、
`Rat.Fractions.Operations.Quotient` は商構成を担当する。

```text
\import \root.Arithmetic[].Rat[] \as R;
\import R.Fractions[] \as RF;
\import RF.Operations[] \as RO;
\import RO.Quotient[] \as RQ;
```

`Rat.Fractions.Operations.Quotient` は証明済みの `FractionEq` を汎用 `Quotient` に渡すので、
同値関係の証明を parameter として要求しない。商上の `add`、`sub`、`mul`、`div` は
代表元を選ばず構成する。`sub` は証明済みの反数と加法から定義するため、独立した
閉包 parameter は不要になった。現在は加法・乗法・除法の image が再び一つの同値類に
なる証明を `Rat.Fractions.Operations.Quotient.ClassClosed` の parameter として要求する。
反数は `fractionNegRespects` と汎用の `UnaryImage` によって閉性まで証明済みであり、
parameter なしの quotient の `neg` として利用できる。商上の `zeroRat` / `oneRat`、
`ofNat` / `ofInteger`、`negInvolutive`、`negZero` も証明済みである。

## 実数と未完了事項

Dedekind 実数は inhabited・proper・lower・rounded・located な切断として定義される。
包含順序の反射・推移・反対称性に加え、狭義順序の非反射性、逆向きの包含との矛盾、
弱順序との左右合成は証明済みである。有理数埋め込み・加法・反数・減法の lower set も
構成済みであり、それらが切断になる証明は `Operations.Closed` の parameter に残る。

Cauchy 実数は有理数列を「差が零へ収束する」関係で割った商である。
`Close` の三角不等式と列同値の反射律・対称律・推移律は証明済みである。
定数列・和・反数の Cauchy 性と同値関係の保存、および商上の加法群の法則も証明済みである。

今後の主な作業は次の通り。

- Rat の商上の加法・乗法・除法について `ClassClosed` の obligation を証明する
- Dedekind の演算が切断を保つことを証明する
- Cauchy の乗法・逆数・順序・完備性を構成する
- 実数の乗法・逆数・完備性を構成する
- `AxiomaticRealStructure` の具体的な項を構成する

## 型検査

```sh
cargo run --quiet -- lib/root.ref
cargo run --quiet -- lib/tests.ref
cargo test --workspace
```

最初の2つはライブラリ定義と公開 API の利用例を型検査する。最後のコマンドは、
処理系の unit test、`.ref` の成功・失敗テスト、doc test をすべて実行する。
