# 実数の形式化

[`Rat.ref`](Rat.ref) は、通常の inductive type と primitive recursor から `Nat`、
自然数対による整数を構成する。`NonZeroInteger = {z : Integer | z != 0}` を積閉集合
`S` とし、分数は `Integer × S` を一要素コンストラクタの inductive type で表す。
`Localization` は `S` 上の乗法と、その台の整数乗法との一致を parameter に取る。
代表元上の `addFraction`、`subFraction`、`mulFraction` は実際に計算する関数であり、
`FractionEq` は整数対の等号を使った交差積である。

`Quotient` は同値関係を parameter に取り、`ClassOf x` として得られる
`Power(Fraction)` だけを refinement した型 `Rat` を作る。演算は代表元を選ばず、
同値類全体の relational image として定義する。`ClassClosed` に congruence の証明を
渡すと `add`、`sub`、`mul : Rat -> Rat -> Rat` が得られる。非零有理数は
`NonZeroRat` refinement として表し、除算は `div : Rat -> NonZeroRat -> Rat` とする。
その relational image は `z * y = x` によって定義する。

[`DedekindReal.ref`](DedekindReal.ref) は、実数を located・rounded Dedekind cut として
定義する。`Rat : Set` と `lt : Rat -> Rat -> Prop` を受け取り、次を構成する。

- 切断の条件 `Inhabited`、`Proper`、`Lower`、`Rounded`、`Located`
- 条件を満たす `Power(Rat)` の refinement type `Real`
- 集合外延性 parameter から得られる kernel 等号 `Eq` と `Le`、`Lt`
- 有理数の埋め込み、加法、反数、減法を与える lower set

[`CauchyReal.ref`](CauchyReal.ref) は `Nat` と `NatLe` を内部で定義し、Cauchy 有理数列の
型 `CauchySeq` と、差が 0 に収束する同値関係 `Equivalent` を定義する。
`Quotient` は反射律・対称律・推移律と集合外延性を parameter に取り、
`ClassOf x = { y | Equivalent x y }` の像を商集合 `Real` とする。そのため
`Real` の要素は代表列ではなく同値類そのものであり、`Eq` は kernel の `=` である。

加法と反数は代表元を選択せず、二つの同値類に属する列の和・反数すべてからなる
relational image として定義する。`SequenceClosed` は列演算が Cauchy 性を保つ証明、
`ClassClosed` はその image が一つの同値類になる証明を parameter に要求する。

[`root.ref`](root.ref) が各 module のルートである。`False`、`Not`、`And`、`Or` は
[`Logic.ref`](Logic.ref) にまとめ、Dedekind側とCauchy側から必要な結合子をimportする。

## 仮定と現在の制限

Dedekind/Cauchy module は引き続き抽象的な `Rat` を引数に取る。`Rat.ref` の具体的な
商を接続するには、自然数算術から `FractionEq` の同値関係則と各演算の congruence
を証明する必要がある。Dedekind cut が実数として期待どおりに振る舞うには、さらに
`lt` が稠密線形順序であり、加法・反数と両立することが必要である。任意の `Rat` と
`lt` だけでは、`Real` が inhabited であることさえ従わない。

`Operations.Closed` は、`RatLower`、`SumLower`、`NegLower` が切断になるという
閉性証明を引数に要求する。`ofRat`、`add`、`neg` はそれぞれの refinement cast に
この証明を明示的に渡す。そのため、これらは有理数側の閉性を仮定した演算であり、
未証明の cast ではない。

kernel の `=` は集合の外延性を自動では使わない。このため両構成とも、対象となる
carrier に特殊化した集合外延性を module parameter として受け取る。Dedekind 側の
`eqByExt` と Cauchy 側の `eqByExt` は、双方向の包含から kernel 等号を構成する。
Dedekind/Cauchy 実数上の乗法・逆数・完備性定理はまだ含めていない。

Cauchy 構成では primitive な quotient type は使わず、`Power(CauchySeq)` のうち
実際に `ClassOf x` として得られる集合だけを refinement して商集合を作る。
`Equivalent` が本当に同値関係になることや、演算が同値類を保つことは `Rat` の
演算名だけからは導けないため、それぞれ明示的な parameter として要求する。

## 確認

```sh
cargo run --quiet -- file tests/reals/root.ref >/dev/null
```

コマンドは各定義と、module parameter として残した obligation の型を検査する。
