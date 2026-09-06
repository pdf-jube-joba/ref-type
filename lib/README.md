# 実数の形式化

[`Nat.ref`](Nat.ref) と [`Bool.ref`](Bool.ref) は Program universe (`\VType`) で
データ型と演算を定義する。Set の式では、同名の型・コンストラクタが自動生成された
Set 側の型・コンストラクタを指す。Program 演算 `add` などに対して、`addSet` は
`\box` / `\Force` による反映、`addPrec` は `\prec` による仕様、
`addMatchesPrec` は両者の一致を表す。証明に `admit` や新しい公理は使っていない。

`addTerminates` は残りの加数について帰納法を使い、任意の accumulator に対する
`\Acc` を証明する。`addMatchesPrec b a` は任意の `a, b` について
`addSet a b = addPrec a b` を証明する。Program の `\Prun` 自体は証明を要求せず、
Set への反映時に停止性を検査する。他の再帰演算も同じ構成を使う。

| ファイル | Program 演算（Set では末尾に `Set`） | 主な証明 |
| --- | --- | --- |
| Nat | `add`, `pred`, `isZero`, `sub` | `MatchesPrec`、加算の零・後者・交換・結合・消去則、減算の零・自己差・加算の消去 |
| Nat | `iter`, `mul`, `pow` | `MatchesPrec`、乗算の零・一・後者・交換・結合・分配則、累乗の零・後者則 |
| Nat | `eqb`, `leb`, `ltb`, `choose`, `min`, `max` | `MatchesPrec`、等値判定の健全性と完全性、`Le` の反射・推移・反対称性、`Lt` の非反射性 |
| Nat | `toggle`, `even`, `odd` | `MatchesPrec` |
| Nat | `divMod`, `div`, `mod`, `gcd` | `MatchesPrec`、商・余りによる復元、余りの上限、GCD の公約数性と最大性 |
| Bool | `neg`, `and`, `or`, `xor`, `implies`, `eqb` | `MatchesPrec`、交換・結合・冪等・吸収・分配則、De Morgan 則、否定の対合、等値判定の健全性と完全性 |

`sub` は零で切り捨てる自然数減算、`pow a zero` は一（`0^0` も一）である。
`iterSet f value count` は `f` を `count` 回適用する。乗算・累乗・偶奇の `Prec` 仕様は
この primitive iterator と、すでに `prec` との一致を証明した下位演算を組み合わせる。
`Le a b` と `Lt a b` は、それぞれ `lebSet a b` と `ltbSet a b` が true になる命題である。
`zeroSet` / `oneSet` は Set 側の定数。Bool の `ite A test yes no` は Set 多相の
条件分岐で、閉じた Program 型を要求する box の制約から直接 `prec` で定義する。

`divMod a b` は Program の自然数対 `NatPair::pair q r` を返し、`div` / `mod` は
その商・余りを取り出す。被除数の後者を一つずつ消費する有限反復で、正の除数に達すると
余りを零に戻して商を増やす。零除数も全域化し、`div a 0 = 0`、`mod a 0 = a` とする。
`divModReconstructs` は全入力で `b * div a b + mod a b = a` を証明し、
`modLt a d` は `mod a (d+1) < d+1` を証明する。零・一に関する法則も公開している。

`gcd a b` は `(a,b) → (b, mod a b)` というユークリッド互除法を使う。第二成分が
零になると状態を保つ。`pairIterTerminates` が反復の停止性を保証し、`gcdIterSettles` は
第二成分の減少から `b` 回の反復で必ず零に達することを証明する。
`gcd a 0 = a`、`gcd 0 b = b`（従って `gcd 0 0 = 0`）である。
`Divides d a` は自然数の因子を持つという構成的な存在命題。
`gcdDividesLeft` / `gcdDividesRight` が GCD の公約数性を、`gcdGreatest` が
任意の公約数は GCD を割り切るという最大性を証明する。これらの証明に公理の追加はない。

`divModPrec` は Set の自然数再帰と `divModNextPrec`、`gcdPrec` は同じく自然数再帰と
`gcdNextPrec` / `modPrec` による仕様であり、各 `MatchesPrec` で Program の反映との一致を示す。
補助演算 `first`, `second`, `pairChoose`, `pairIter`, `divModNext`, `gcdNext` にも
反映・仕様・一致証明がある。自然数は単項表現で、互除法の反復も第二引数の値だけ行うため、
大きな具体値の計算には適していない。

`Rat.ref` 内の独自の Set 自然数との統合は別途必要であり、この変更だけで有理数の
obligation が解消するわけではない。

[`Int.ref`](Int.ref) は Program の整数を `Int::ofNat n`（非負整数）と
`Int::negSucc n`（`-(n+1)`）の直和 `Nat + Nat` で表す。零の表現は一つである。

Set 側には三つの層がある。

- `Int` と `*Set`: Program の型と演算の reflection。
- `*Prec`: primitive recursor と検証済みの Nat 演算による仕様。
- `Grothendieck` と `*Math`: 加法モノイド `(Nat,+,0)` の群完成。

数学的構成では、自然数対 `Difference` の `(a,b)` と `(c,d)` を `a+d=c+b` で同一視する。
この同値関係の三法則を証明し、`Power(Difference)` 内の同値類そのものを refinement して
商集合を作る。`diffPrec` による正規化が代表元に依存しないことを示し、
`toMath` / `fromMath` の両方向の逆写像則を `fromTo` / `toFrom` として証明する。
`fromMath` は一意な値を取り出す `\take` を使う。新しい公理や `admit`、未証明の
閉性 parameter は使わず、同値類の等号には既存の `\axiom:setext` を使う。

商上の加算・反数・乗算は自然数対の通常の公式で定義し、`*RepRespects` と
`*MathClass` が任意の代表元についての整合性を保証する。補助演算は商の一意な正規形で定義する。
各公開演算の `*MatchesPrec` と `*MatchesMath` が Program の reflection、仕様、商上の演算の一致を表す。
例えば `addMatchesMath x y` は `toMath (addSet x y) = addMath (toMath x) (toMath y)` である。

| 整数の演算 | 内容 |
| --- | --- |
| `zero`, `one`, `minusOne`, `ofNat`, `negOfNat`, `diff` | 定数・自然数の埋め込み・自然数対の差 |
| `neg`, `add`, `sub`, `mul`, `succ`, `pred` | 符号付き算術 |
| `pow` | 自然数指数の累乗。`0^0 = 1` |
| `positive`, `negative`, `natAbs`, `abs`, `sign` | 非負・負の成分、絶対値、`-1/0/1` の符号 |
| `isZero`, `eqb`, `leb`, `ltb`, `choose`, `min`, `max` | 判定・選択。`Le` / `Lt` は判定が true になる命題 |
| `even`, `odd` | 負の整数も含む偶奇判定 |

加法の零・交換・結合・逆元則を商側で証明している。この整数 API は基本算術と判定を対象とし、
整数の除算・剰余・GCD はまだ含めていない。既存の `Rat.ref` の整数表現の置換は行っていない。

module import は型の instance を作るため、`Int` 内の Nat / Bool と別に import した型は混ぜない。
Set 側では公開 alias `Int.Nat` / `Int.Bool` を使える。`natZero!{}`、`natSucc!{n}`、
`boolTrue!{}`、`boolFalse!{}` は `\use` して使うマクロで、Program / Set の両方から
同じ instance のコンストラクタを参照できる。具体例は `tests.ref` の `IntegerExamples` を参照。

[Pair.ref](Pair.ref) は型引数 `A, B : Set` を取る直積 `Times[A, B]` を
一要素コンストラクタの inductive type として定義する。module parameter は使わず、
`pair`、`first`、`second` などが通常の引数として `A` と `B` を取る。それぞれの
β則、pair の η則、二つの射影が等しい pair は等しいという外延性を証明する。

[`AxiomaticReals.ref`](AxiomaticReals.ref) は、台集合上の零、一、四則演算、逆数と
`Power(Times)` で表した二項順序関係を named field を持つ proof-free な
Bourbaki structure `RawRealStructure` として定義する。体、線形順序、順序との両立、上限性の条件は
`IsAxiomaticRealStructure` にまとめ、条件を満たす構造を refinement type
`AxiomaticRealStructure` とする。

[`Rat.ref`](Rat.ref) は、inductive type と primitive recursor から `Nat` を構成し、
自然数対による整数と正の分母を持つ分数代表は named-field structure として定義する。`Fraction` が保持する
分母 `d` は実際の分母 `d + 1` を表すため、零分母は構文的に作れない。これにより
`zero`、`one`、`lt`、`add`、`neg`、`sub`、`mul` は証明 parameter なしの具体的な
定義になっている。

`FractionEq` は交差積による代表元の等価関係である。反射律 `fractionEqRefl` と
対称律 `fractionEqSym` は証明済みで、推移律は自然数の加法の交換・結合・消去律が
必要な obligation として `Quotient` に残している。`Quotient` は `FractionEq` の
同値類を `Power(Fraction)` の refinement として表し、その等号には
`\axiom:setext` を使う。演算は同値類全体の relational image で定義し、
`ClassClosed` に congruence の証明を渡す。

[`DedekindReal.ref`](DedekindReal.ref) は module parameter を取らず `Rat.ref` を import し、
実数を located・rounded Dedekind cut として定義する。切断の membership が
`FractionEq` の代表元に依存しないことも `RespectsFractionEq` として条件に含める。
次を構成する。

- 切断の条件 `Inhabited`、`Proper`、`Lower`、`Rounded`、`Located`
- 条件を満たす `Power(Rat)` の refinement type `Real`
- `Le`、`Lt` と、`Le` の反射律・推移律
- `\axiom:setext` による kernel 等号と反対称律
- 有理数の埋め込み、加法、反数、減法を与える lower set

[`CauchyReal.ref`](CauchyReal.ref) も module parameter を取らず `Rat.ref` を import する。
`Rat.ref` の `Nat` と `NatLe` を共通の添字基盤として使い、Cauchy 有理数列の型 `CauchySeq` と、差が 0 に
収束する同値関係 `Equivalent` を定義する。距離条件は `abs` を別の演算として
受け取らず、`x - y < eps` と `y - x < eps` の連言 `Close` で表す。
`Quotient` は反射律・対称律・推移律を parameter に取り、集合外延性には
`\axiom:setext` を使って、
`ClassOf x = { y | Equivalent x y }` の像を商集合 `Real` とする。そのため
`Real` の要素は代表列ではなく同値類そのものであり、`Eq` は kernel の `=` である。

加法と反数は代表元を選択せず、二つの同値類に属する列の和・反数すべてからなる
relational image として定義する。`SequenceClosed` は列演算が Cauchy 性を保つ証明、
`ClassClosed` はその image が一つの同値類になる証明を parameter に要求する。

[`root.ref`](root.ref) が各 module のルートである。`False`、`Not`、`And`、`Or` は
[`Logic.ref`](Logic.ref) にまとめる。`And` は二つの証明を named field に持つ structure であり、
`not!`、`and!`、`and4!` などのマクロを各構成から必要に応じて `\use` する。

## 記述上の方針

単なるデータの束には `\structure` を使い、帰納法が必要な型だけを `\inductive` にする。
このため `RawRealStructure`、`Integer`、`Fraction`、`FinitePair`、`And` は structure、
`Nat`、`Or`、Cartesian product `Times` は inductive type である。structure の値は
field 名付きで構築する。

反復する論理結合は `Logic.ref` の hygienic macro に集約する。型引数が使用箇所から一意に決まる場合は
`_` の implicit metavariable を使う一方、公開定義の型は明示してモジュール境界を読みやすく保つ。

## 公理的実数への接続と現在の制限

`AxiomaticReals.ref` の `LinearOrderLaws` のうち、Dedekind 側の反射律と推移律は
`leRefl`、`leTrans` として証明済みである。反対称律も `\axiom:setext` を使う
`leAntisym` として証明済みである。しかし、現在の `LinearOrderLaws` が要求する
`Le x y \/ Le y x` は古典的な全順序性であり、located cut と現在の constructive な
`Logic.Or` だけからは導けない。

さらに、どちらの実数構成にも乗法・逆数がまだなく、Dedekind 側の上限構成と
Cauchy 側の完備性も未証明である。Cauchy 側では、`Equivalent` の同値関係則と
列演算の閉性を有理数算術から示す必要があり、完備性の証明では可算選択に
相当する原理も問題になる。このため、現時点で `AxiomaticRealStructure` の項そのものを
構成するところまでは到達していない。

`Rat.ref` 側で残る最初の基礎 obligation は、`FractionEq` の推移律、四則演算の
congruence、`lt` の稠密線形順序性と演算との両立性である。Nat.ref には加法の結合・交換・消去律を追加済みだが、
Rat.ref の独自の自然数型に接続する作業が残っている。

`Operations.Closed` は、`RatLower`、`SumLower`、`NegLower` が切断になるという
閉性証明を引数に要求する。`ofRat`、`add`、`neg` はそれぞれの refinement cast に
この証明を明示的に渡す。そのため、これらは有理数側の閉性を仮定した演算であり、
未証明の cast ではない。

kernel の `=` は集合の外延性を自動では使わないため、Rat・Dedekind・Cauchy の
`eqByExt` はいずれも双方向の包含を `\axiom:setext` に渡して kernel 等号を構成する。
Dedekind/Cauchy 実数上の乗法・逆数・完備性定理はまだ含めていない。

Cauchy 構成では primitive な quotient type は使わず、`Power(CauchySeq)` のうち
実際に `ClassOf x` として得られる集合だけを refinement して商集合を作る。
`Equivalent` が本当に同値関係になることや、演算が同値類を保つことは `Rat` の
演算名だけからは導けないため、それぞれ明示的な parameter として要求する。

## 確認

```sh
cargo run --quiet -- lib/root.ref
cargo run --quiet -- lib/tests.ref
cargo test --workspace
```

コマンドは各定義と、module parameter として残した obligation の型を検査する。
