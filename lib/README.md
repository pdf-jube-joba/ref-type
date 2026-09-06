# 標準ライブラリと実数の形式化

`root.ref` がライブラリのモジュール一覧、`tests.ref` が利用例を兼ねた型検査用のルートである。
証明に `admit` や新しい公理は追加していない。商集合と切断の等号には既存の
`\axiom:setext`、整数の一意な正規形の取り出しには `\take` を使う。

## 定義の配置

| 層 | ファイル | 責務 |
| --- | --- | --- |
| 論理 | [Logic.ref](Logic.ref) | `False`、`Not`、`And`、`Or` と論理結合の記法 |
| 等式 | [Equality.ref](Equality.ref)、[Equality/Laws.ref](Equality/Laws.ref) | 任意の台集合上の対称律・推移律・transport・一〜三引数の合同則 |
| 直積 | [Pair.ref](Pair.ref) | Program の `Times` と Set 側の構築・射影・交換・写像・カリー化 |
| 直積の法則 | [Pair/Laws.ref](Pair/Laws.ref)、[Pair/MapLaws.ref](Pair/MapLaws.ref)、[Pair/FunctionLaws.ref](Pair/FunctionLaws.ref) | β・η・外延性、写像の合成、カリー化の逆写像則 |
| 有限部分集合 | [Finset.ref](Finset.ref) | 一点集合・二点集合と所属の証明。対のデータ型は定義しない |
| 商集合 | [Quotient.ref](Quotient.ref) | 関係とその同値関係則から、同値類の集合・商の台集合・外延性を構成 |
| データと算術 | [Bool.ref](Bool.ref)、[Nat.ref](Nat.ref)、[Int.ref](Int.ref) | Program 演算、Set への反映、仕様、一致証明、型固有の法則 |
| 有理数の代表元 | [Rat.ref](Rat.ref) | 共通の Nat 上の整数対と、正の分母を持つ分数の算術 |
| 有理数の商 | [Rat/Quotient.ref](Rat/Quotient.ref)、[Rat/Quotient/ClassClosed.ref](Rat/Quotient/ClassClosed.ref) | 汎用商の適用、同値類上の演算、閉性を仮定した精密化 |
| Dedekind 切断 | [DedekindReal.ref](DedekindReal.ref)、[DedekindReal/Operations.ref](DedekindReal/Operations.ref) | 切断と順序、算術 lower set。閉性の仮定は `Operations/Closed.ref` |
| Cauchy 列 | [CauchyReal.ref](CauchyReal.ref)、[CauchyReal/Quotient.ref](CauchyReal/Quotient.ref) | Cauchy 性、列の同値関係、汎用商の適用 |
| Cauchy 列の演算 | [CauchyReal/Quotient/Operations.ref](CauchyReal/Quotient/Operations.ref) 以下 | 列演算、`SequenceClosed` による Cauchy 性、`ClassClosed` による商上の閉性 |
| 実数の仕様・古典原理 | [AxiomaticReals.ref](AxiomaticReals.ref)、[Classical.ref](Classical.ref) | 公理的実数の構造。Classical は現在、将来の構成についての注記のみ |

汎用の論理・等式・直積・商の構成を数のモジュールから独立させる。一方、Program の
状態機械・停止性証明・反映・`Prec` 仕様・`MatchesPrec` は対応を追えるよう近くに置く。
算術の `succCong` や `addCong` は型固有の名前として残し、証明は共通の合同則を使う。

入れ子モジュールのファイルは、その論理上のパスに合わせて配置する。
例えば `Rat.ref` の `\module Quotient(...);` は `Rat/Quotient.ref` を読む。
ファイルを分けるだけで新しい import を挟まず、元のスコープと型の同一性を保つ。

## 等式の使い方

```text
\import \root.Equality() \as Equality;
\use Equality.sym;
\use Equality.trans;
\use Equality.congr;
```

`trans!{Nat} a b c ab bc` は `a = c`、`congr!{A B} f a b ab` は `f a = f b` を証明する。
`congr2!{A B C}` と `congr3!{A B C D}` は成分ごとに等しい引数を持つ関数の合同則である。
`transport!{A} P a b ab pa` は `P a` を `P b` に移す。

現在の PTS は命題内で `Set` 自体を量化しないため、台集合はマクロ展開時に指定する。
テンプレートには明示的な型を付け、`_` で省略した等式の両辺も推論できるようにしている。
`Equality/Laws.ref` は同じテンプレートを任意の台集合で型検査し、名前付きの API も提供する。
例えば `\import \root.Equality().Laws(A := X) \as E;` で `E.sym`、`E.trans` を使える。

数のモジュールではマクロを使う。現状の import は型のインスタンスを作り直すため、
同じモジュールで宣言した型を引数にする補助モジュールの import を増やすと、外側の再 import 時に
型の対応が崩れる場合がある。テンプレートを使用箇所で具体化すると、この問題を避けられる。

## 直積と有限部分集合

`Times(A, B: \VType): \VType` は一つの Program データ型であり、Set 側の型と
コンストラクタを自動生成する。Set 側の `Times[A, B]` は任意の `A, B: Set` に使える。

- `pair A B a b`、`first A B p`、`second A B p`: 構築と射影。
- `swap A B p`: 成分の交換。
- `map A B C D f g p`: 各成分への関数適用。
- `curry A B C f`、`uncurry A B C f`: 対を取る関数と二引数関数の変換。

法則には射影の β 則、対の η 則と外延性、交換の対合、写像の恒等・合成則、
カリー化の点ごとの逆写像則がある。Program の具体的な射影と、その反映との一致は
`tests.ref` の `PairExamples` に例がある。現在の処理系では型引数付き Program モジュールの
反映証明と Program マクロに制約があるため、`Nat.first` / `Nat.second` は具体型で定義する。

`NatPair`、整数の形式差 `Difference`、有理数の分子代表 `Integer` は、この直積の Set alias である。
`Nat.natPair`、`Int.pair`、`Rat.integer` は各用途の構築関数であり、別の対型を宣言しない。

`Finset(A: Set)` は `Power(A)` 上の `singleton` と `pair` を提供する。
それぞれ `inSingleton`、`inPairLeft`、`inPairRight` で所属を証明できる。
これは有限集合の初歩的な構成であり、一般の有限性の述語や濃度までは定義していない。

## Program 演算と仕様

Bool・Nat・Int のデータ型は `\VType` に置く。Set の式で同名の型・コンストラクタを参照すると、
自動生成された Set 側を使う。Program 演算 `add` に対し、`addSet` は `\box` / `\Force` による反映、
`addPrec` は primitive recursor による仕様、`addMatchesPrec` は両者の一致を表す。
Program の `\Prun` 自体は部分計算を許し、Set に反映するときに停止性を検査する。

| 型 | 演算 | 主な証明 |
| --- | --- | --- |
| Nat | `add`, `pred`, `isZero`, `sub` | 零・後者則、加法の交換・結合・消去、切り捨て減算 |
| Nat | `iter`, `mul`, `pow` | 有限反復、乗法の交換・結合・分配、累乗の零・後者則 |
| Nat | `eqb`, `leb`, `ltb`, `choose`, `min`, `max` | 等値判定、`Le` の反射・推移・反対称性、`Lt` の非反射性 |
| Nat | `toggle`, `even`, `odd` | Program と `Prec` の一致 |
| Nat | `divMod`, `div`, `mod`, `gcd` | 商・余りによる復元、余りの上限、GCD の公約数性と最大性 |
| Bool | `neg`, `and`, `or`, `xor`, `implies`, `eqb` | 交換・結合・冪等・吸収・分配、De Morgan 則、否定の対合、等値判定 |
| Int | 定数、`ofNat`, `negOfNat`, `diff`, `neg`, `add`, `sub`, `mul`, `succ`, `pred`, `pow` | Program・仕様・群完成上の演算の一致、加法の群の法則 |
| Int | 符号・絶対値・比較・選択・偶奇 | `positive`, `negative`, `natAbs`, `abs`, `sign`, `isZero`, `eqb`, `leb`, `ltb`, `choose`, `min`, `max`, `even`, `odd` |

`sub` は零で切り捨て、`0^0 = 1` とする。零除数では `div a 0 = 0`、`mod a 0 = a`。
`divMod` は共通の対型で商と余りを返す。`gcd` はユークリッド互除法を有限反復で実装し、
第二成分の減少により反復が収束することを証明する。自然数は単項表現なので、大きな具体値の計算には向かない。
`Divides d a` は自然数の因子を証拠として持つ構成的な存在命題である。

Int は `ofNat n` と `negSucc n`（`-(n+1)`）で表し、零の表現は一つだけである。
数学的には自然数対 `(a,b)` と `(c,d)` を `a+d=c+b` で同一視し、その同値類から
群完成 `Grothendieck` を作る。`toMath` / `fromMath` は相互に逆で、
`*MatchesMath` が Program 演算と群完成上の演算を結ぶ。整数の除算・剰余・GCD はまだない。

module import ごとに型の instance が作られるため、別々に import した Nat / Bool を混ぜない。
Int が公開する `Nat` / `Bool` alias と、`natZero!{}`、`natSucc!{n}`、`boolTrue!{}`、
`boolFalse!{}` のマクロは同じ instance を参照する。

## 有理数・実数と残る証明

Rat の `Nat`、`natAdd`、`natMul`、`NatLe`、`NatLt` は共通の Nat ライブラリを使う。
`natLeRefl` / `natLeTrans` も共通の順序則を公開する。Cauchy 列の添字もこの自然数である。
有理数の分子は形式差の対、分数 `Fraction` は named-field structure であり、
分母として保持する `d` は実際の分母 `d+1` を表す。零分母は構文的に作れない。

`FractionEq` は交差積による同値関係である。反射律・対称律は証明済みだが、
推移律と商上の演算の閉性は引き続き parameter として要求する。
Nat の共有により算術の証明を利用できる基盤は揃ったが、分数のこれらの証明自体は未完了である。

汎用 `Quotient` は台集合・関係・同値関係則を受け取り、`ClassOf x` の像を
`Power(A)` の refinement として表す。Rat と CauchyReal はその構成を使い、
それぞれの `Quotient` ファイルには語彙の alias と算術固有の構成だけを置く。
演算は代表元を選ばず同値類全体の relational image として定義し、
`ClassClosed` がその image が再び一つの同値類になる証明を受け取る。

Dedekind 実数は inhabited・proper・lower・rounded・located で、分数の代表元に依存しない切断である。
包含による順序の反射・推移・反対称性は証明済みで、lower set 上に有理数の埋め込み・加法・反数・減法を構成する。
`Operations.Closed` はこれらが切断になる閉性証明を要求する。

Cauchy 実数は有理数列を差が零に収束する関係で割った商である。
同値関係則、列演算の Cauchy 性、商上の閉性は parameter に残る。
どちらの実数にも乗法・逆数・完備性の証明がまだなく、
`AxiomaticRealStructure` の具体的な項の構成には到達していない。

## API の整理による変更

- `Nat.eqSym` / `eqTrans` / `congr`、Int の型別の合同則は `Equality` の共通 API に移した。
- `Nat.NatPair::pair` の代わりに Set では `Nat.natPair` を使う。
- Rat の独自の Nat / NatLe / NatLt と、そのコンストラクタは共通の Nat と順序に置き換えた。
- `Integer` / `Difference` は直積の alias に変わったため、構築・射影には公開関数を使う。
- `Finset.FinitePair` とその射影は廃止した。データの対は `Pair`、有限部分集合は `Finset(A := ...)` を使う。

## 確認

```sh
cargo run --quiet -- lib/root.ref
cargo run --quiet -- lib/tests.ref
cargo test --workspace
```

これらは証明済みの定義と、parameter として残した obligation の型を検査する。
