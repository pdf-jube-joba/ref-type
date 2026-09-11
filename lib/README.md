# 標準ライブラリ

`root.ref` は公開モジュールの一覧、`tests.ref` は利用例を兼ねたライブラリ全体の型検査である。
現在の処理系には任意の証明を通す `admit` / `sorry` はない。処理系が持つ組み込み公理は、
必要な前提を検査する `\axiom:setext`、`\axiom:funext`、
`\axiom:classicalIndefiniteChoice` の3つである。現在の `lib/` が実際に使うのは `setext` だけである。

## モジュール構成

| 分野 | ファイル | 内容 |
| --- | --- | --- |
| 論理 | [Logic.ref](Logic.ref) | `False`、`Not`、`And`、`Or` と記法 |
| 等式 | [Equality.ref](Equality.ref)、[Equality/Laws.ref](Equality/Laws.ref) | 対称律、推移律、transport、合同則 |
| 直積 | [Pair.ref](Pair.ref) と `Pair/` 以下 | 構築・射影・交換・写像・カリー化とその法則 |
| 有限部分集合 | [Finset.ref](Finset.ref) | 一点集合と二点集合 |
| 商集合 | [Quotient.ref](Quotient.ref) | 同値類、商の台集合、演算の relational image |
| 基本データ | [Bool.ref](Bool.ref)、[Nat.ref](Nat.ref) と `Nat/` 以下、[Int.ref](Int.ref) と `Int/` 以下、[IntAlgebra.ref](IntAlgebra.ref) | Program 演算、Set への反映、仕様と法則、整数の代数構造 |
| 代数構造 | [Monoid.ref](Monoid.ref)、[Algebra.ref](Algebra.ref) | Monoid、Group、Semiring、Ring、Field |
| 有理数 | [Rat.ref](Rat.ref) と `Rat/` 以下 | 分数代表、同値関係、商上の演算 |
| Dedekind 実数 | [DedekindReal.ref](DedekindReal.ref) とその子モジュール | 切断、順序、lower set 上の演算 |
| Cauchy 実数 | [CauchyReal.ref](CauchyReal.ref) とその子モジュール | Cauchy 列、商、点ごとの演算 |
| 実数の仕様 | [AxiomaticReals.ref](AxiomaticReals.ref) | 公理的実数構造 |

入れ子モジュールは論理上のパスと同じ場所に置く。例えば
`Rat/Fractions/Operations.ref` の `\module Quotient;` の本体は
`Rat/Fractions/Operations/Quotient.ref` にある。子ファイルは親のスコープを引き継ぐので、
同じ依存を改めて import して型の instance を作り直さない。

## 等式と合同則

等式の基本操作は carrier をマクロ引数にして使用する。

```text
\import \root.Equality() \as Equality;
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
congr2!{Nat Nat Nat} natAdd _ _ _ _ leftEq rightEq
```

したがって、単に二引数関数へ等式を写すだけのローカル補題は通常不要である。
`Nat.addCong` のような型固有の名前は公開 API として残すが、数の証明内部では
`congr!` / `congr2!` / `congr3!` を直接使える。

固定した carrier の名前付き API が必要なら、次の形も使える。

```text
\import \root.Equality().Laws(A := X) \as E;
```

現在の PTS では命題内で `Set` 自体を量化しないため、carrier はマクロ展開時に指定する。
また module import は生成的であり、import ごとに別の型 instance を作る。
同じモジュールで宣言した型に対しては、補助モジュールを再 import するより、
使用箇所で等式マクロを具体化する方が安全である。

## 代数構造

`Monoid(Carrier := A)` は `RawMonoid` と `MonoidLaws` を分離し、両者を満たす値を
refinement `Monoid` として表す。`CommutativeMonoid` も同じ raw data を使う。
`monoidLawsIntro` と `commutativeMonoidLawsIntro` は法則レコードの構築を補助する。

`Algebra(Carrier := A)` は次の構造を提供する。

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

`Pair.Times(A, B: \VType): \VType` が Program の対を定義し、その Set 表現も自動生成する。
Set 側では次を使う。

- `pair A B a b`、`first A B p`、`second A B p`
- `swap A B p`
- `map A B C D f g p`
- `curry A B C f`、`uncurry A B C f`

`NatPair`、Int の `Difference`、Rat の `Integer` はすべてこの対型の alias であり、
用途ごとに別の対データ型を宣言しない。

`Finset(A := A)` は `Power(A)` 上の `singleton` と `pair`、および各要素の所属証明を提供する。
一般の有限性述語や濃度はまだ扱わない。

## 商への演算の持ち上げ

`Quotient` は、同値関係を保つ単項・二項演算のために `UnaryRespects` / `BinaryRespects`、
`UnaryImage` / `BinaryImage` を提供する。`induction` は商についての命題を代表元の場合へ帰着する。
`unaryImageClass` / `binaryImageClass` は代表元上の
image が期待する同値類に一致することを示し、`unaryImageClosed` / `binaryImageClosed` は
image が再び商の要素になることを示す。演算ごとに同じ外延性証明を作り直す必要はない。

## Program 演算と仕様

Bool・Nat・Int は `\VType` の Program データである。各演算には原則として次の層がある。

- `add`: Program 演算
- `addSet`: `\box` / `\Force` による Set への反映
- `addPrec`: primitive recursor による仕様
- `addMatchesPrec`: 反映した演算と仕様の一致

`\Prun` は部分計算を表せるが、Set に反映する際には停止性証明が必要になる。

Nat は加減乗除、累乗、比較、有限反復、偶奇、GCD を持つ。除数が零なら
`div a 0 = 0`、`mod a 0 = a` とし、`0^0 = 1` とする。自然数は単項表現なので、
大きな具体値の評価には向かない。

Program 演算とその直接の仕様は `Nat` 本体に置き、一般の算術法則は `Nat.Laws`、
除算・剰余・GCD の再構成則・剰余の上界・最大公約数の法則は
`Nat.Laws.Division` に分離している。親と同じ Nat instance を使うには、次のように
import 済み instance から child を順に開く。

```text
\import \root.Nat() \as N;
\import N.Laws() \as NL;
\import NL.Division() \as ND;
```

Int は `ofNat n` と `negSucc n` からなる一意な Program 正規形を持つ。
数学側では自然数対 `(a,b)` を `a+d=c+b` で同一視した群完成 `Grothendieck` を構成し、
`toMath` / `fromMath` と `*MatchesMath` が Program 演算との対応を与える。
加法の結合則と乗法の可換律も、この対応を通して具体的な `Int` 上へ戻してある。
整数の除算・剰余・GCD は未実装である。

群完成とその上の演算は `Int.Math`、Program 仕様との対応は
`Int.Math.Specification`、代数法則は `Int.Math.Specification.Laws` に分離している。

```text
\import \root.Int() \as I;
\import I.Math() \as IM;
\import IM.Specification() \as IS;
\import IS.Laws() \as IL;
```

Program の逐次計算は `\block` 内の `\bind` 文で記述する。各 block は最後に
`\return value;` を置き、旧来の深く入れ子になった `\bind ... \in ...` は使わない。

別々に import した Nat / Bool の instance は混ぜられない。Int と組み合わせる場合は、
Int が公開する `Nat` / `Bool` alias と `natZero!{}`、`natSucc!{n}`、
`boolTrue!{}`、`boolFalse!{}` を使う。

## 有理数

Rat の分子 `Integer` は自然数対による形式差である。`IntegerEq` は同値関係であり、
`addIntegerRespects`、`negIntegerRespects`、`subIntegerRespects`、
`mulIntegerRespects` が各演算の代表元独立性を与える。

`Fraction` は分子と `denominatorIndex` を保持する。index `d` は実際の分母 `d+1` を表すため、
零分母は構文的に作れない。`FractionEq` は交差積による同値関係である。
推移律 `fractionEqTrans` では `Nat.mulCancelRightSucc` を使い、中央の正の分母を消去する。

`Rat` は形式整数、`Rat.Fractions` は正分母の分数代表、
`Rat.Fractions.Operations` は分数演算、
`Rat.Fractions.Operations.Quotient` は商構成を担当する。

```text
\import \root.Rat() \as R;
\import R.Fractions() \as RF;
\import RF.Operations() \as RO;
\import RO.Quotient() \as RQ;
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
`Close` と列同値の対称律は証明済みである。反射律・推移律、列演算の Cauchy 性、
商上の閉性は parameter に残る。

今後の主な作業は次の通り。

- Rat の商上の加法・乗法・除法について `ClassClosed` の obligation を証明する
- Dedekind の演算が切断を保つことを証明する
- Cauchy の同値関係の反射律・推移律、列演算、商演算の閉性を証明する
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
