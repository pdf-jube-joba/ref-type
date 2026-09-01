# 実数の形式化

[`Pair.ref`](Pair.ref) は module parameter `A, B : Set` に対する直積 `Times` を
一要素コンストラクタの inductive type として定義する。`first`、`second` とそれぞれの
β則、pair の η則、二つの射影が等しい pair は等しいという外延性を証明する。

[`AxiomaticReals.ref`](AxiomaticReals.ref) は、台集合上の零、一、四則演算、逆数と
`Power(Times)` で表した二項順序関係を proof-free な Bourbaki 構造
`RawRealStructure` として定義する。体、線形順序、順序との両立、上限性の条件は
`IsAxiomaticRealStructure` にまとめ、条件を満たす構造を refinement type
`AxiomaticRealStructure` とする。

[`Rat.ref`](Rat.ref) は、通常の inductive type と primitive recursor から `Nat`、
自然数対による整数、正の分母を持つ分数代表を構成する。`Fraction` が保持する
分母 `d` は実際の分母 `d + 1` を表すため、零分母は構文的に作れない。これにより
`zero`、`one`、`lt`、`add`、`neg`、`sub`、`mul` は証明 parameter なしの具体的な
定義になっている。

`FractionEq` は交差積による代表元の等価関係である。反射律 `fractionEqRefl` と
対称律 `fractionEqSym` は証明済みで、推移律は自然数の加法の交換・結合・消去律が
必要な obligation として `Quotient` に残している。`Quotient` は `FractionEq` の
同値類を `Power(Fraction)` の refinement として表す。演算は同値類全体の
relational image で定義し、`ClassClosed` に congruence の証明を渡す。

[`DedekindReal.ref`](DedekindReal.ref) は module parameter を取らず `Rat.ref` を import し、
実数を located・rounded Dedekind cut として定義する。切断の membership が
`FractionEq` の代表元に依存しないことも `RespectsFractionEq` として条件に含める。
次を構成する。

- 切断の条件 `Inhabited`、`Proper`、`Lower`、`Rounded`、`Located`
- 条件を満たす `Power(Rat)` の refinement type `Real`
- `Le`、`Lt` と、`Le` の反射律・推移律
- `Extensionality` module に集合外延性を渡した場合の kernel 等号と反対称律
- 有理数の埋め込み、加法、反数、減法を与える lower set

[`CauchyReal.ref`](CauchyReal.ref) も module parameter を取らず `Rat.ref` を import する。
`Nat` と `NatLe` を内部で定義し、Cauchy 有理数列の型 `CauchySeq` と、差が 0 に
収束する同値関係 `Equivalent` を定義する。距離条件は `abs` を別の演算として
受け取らず、`x - y < eps` と `y - x < eps` の連言 `Close` で表す。
`Quotient` は反射律・対称律・推移律と集合外延性を parameter に取り、
`ClassOf x = { y | Equivalent x y }` の像を商集合 `Real` とする。そのため
`Real` の要素は代表列ではなく同値類そのものであり、`Eq` は kernel の `=` である。

加法と反数は代表元を選択せず、二つの同値類に属する列の和・反数すべてからなる
relational image として定義する。`SequenceClosed` は列演算が Cauchy 性を保つ証明、
`ClassClosed` はその image が一つの同値類になる証明を parameter に要求する。

[`root.ref`](root.ref) が各 module のルートである。`False`、`Not`、`And`、`Or` は
[`Logic.ref`](Logic.ref) にまとめ、Dedekind側とCauchy側から必要な結合子をimportする。

## 公理的実数への接続と現在の制限

`AxiomaticReals.ref` の `LinearOrderLaws` のうち、Dedekind 側の反射律と推移律は
`leRefl`、`leTrans` として証明済みである。反対称律は集合外延性を受け取る
`Extensionality.leAntisym` まで接続できた。しかし、現在の `LinearOrderLaws` が要求する
`Le x y \/ Le y x` は古典的な全順序性であり、located cut と現在の constructive な
`Logic.Or` だけからは導けない。

さらに、どちらの実数構成にも乗法・逆数がまだなく、Dedekind 側の上限構成と
Cauchy 側の完備性も未証明である。Cauchy 側では、`Equivalent` の同値関係則と
列演算の閉性を有理数算術から示す必要があり、完備性の証明では可算選択に
相当する原理も問題になる。このため、現時点で `AxiomaticRealStructure` の項そのものを
構成するところまでは到達していない。

`Rat.ref` 側で残る最初の基礎 obligation は、`FractionEq` の推移律、四則演算の
congruence、`lt` の稠密線形順序性と演算との両立性である。これらには自然数加法の
結合・交換・消去律から始める必要がある。

`Operations.Closed` は、`RatLower`、`SumLower`、`NegLower` が切断になるという
閉性証明を引数に要求する。`ofRat`、`add`、`neg` はそれぞれの refinement cast に
この証明を明示的に渡す。そのため、これらは有理数側の閉性を仮定した演算であり、
未証明の cast ではない。

kernel の `=` は集合の外延性を自動では使わない。Dedekind 側では外延性を
`Extensionality` に切り出し、Cauchy 側では実際の商を作る `Quotient` の parameter に残した。
`eqByExt` はどちらも双方向の包含から kernel 等号を構成する。
Dedekind/Cauchy 実数上の乗法・逆数・完備性定理はまだ含めていない。

Cauchy 構成では primitive な quotient type は使わず、`Power(CauchySeq)` のうち
実際に `ClassOf x` として得られる集合だけを refinement して商集合を作る。
`Equivalent` が本当に同値関係になることや、演算が同値類を保つことは `Rat` の
演算名だけからは導けないため、それぞれ明示的な parameter として要求する。

## 確認

```sh
cargo run --quiet -- file lib/root.ref >/dev/null
```

コマンドは各定義と、module parameter として残した obligation の型を検査する。
