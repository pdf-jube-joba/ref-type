# 言語で書きたい構成と比較例

最小例と対照例は [比較サンプル一覧](fix-md/README.md#対象文書の対応) にまとめる。
G01〜G04 と G11 の `.ref` は、全文を playground.md に貼り付けて単独で検査できる。
比較する条件と現在の結果は各項目のリンク先に記載する。
Box の検討は [Box の parameter](box-parameters.md#g11) に分けている。

<a id="g01"></a>

## G01: record eta 則

record の変数 `s` と、各フィールドを射影して再構成した record を、定義的に等しいものとして扱いたい。

[最小比較: G01](fix-md/README.md#g01) は、変数と具体的な record に対して同じ等式を `refl` で検査する。
変数では `types are not convertible` で失敗し、具体値では成功する。

法則を含む `\Set` の structure はデータ・法則・部分集合型へ展開されるため、公開された型に直接 `\induction` を適用してデータの constructor を指定することはできない。
[実数値線形写像](../libs/calculus/src/Real/Multivariable/Differential/Def.ref)は `LinearData` と `LinearLaws` を明示的に分け、通常のデータ record の帰納法から再構成の等式を示す。

<a id="g02"></a>

> [!note]
> これは対応しなくていいかな。
> この gaps には残しておかないと、あとで同じものが記載されうるので残しておきます。

## G02: 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

[最小比較: G02](fix-md/README.md#g02) は、同じ証明引数と集合値について、通常の関数と contextual な定義を比較する。
通常の関数型 `P -> A` は sort の積規則で失敗し、contextual な `choose(h: P): A` は成功する。

滑らかな遷移写像の互換性から写像の値を作る構成を、`Compatible -> Maps.Map U V` の型と lambda で書きたい。
この型は `Prop` から `Set` への積になるため、現在の積規則では `no product rule` になる。
[`Atlas.Pair.smoothMap`](../libs/manifolds/src/Dimension/Atlas.ref) のように証明を宣言の明示的な引数へ移すと、同じ構成を記述できる。
小さいアトラスから滑らかな多様体を作る `Smooth.From.manifold` と、鳩の巣原理の証明で使う有限添字の縮小にもこの表現を適用している。
定理の仮定は命題全体の量化に含め、集合値を返す構成関数と区別する。

<a id="g03"></a>

> [!note]
> 保留します。
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい気がするので。

## G03: 関係を parameter に持つ record の集合値の射影

関係 `relation: A -> A -> \Prop` を Box parameter に持つ集合値の record に、データとその関係に関する法則をまとめたい。
有限選択の結果では、選択した有限集合と、元の集合との対応を表す法則を一つの record として扱いたい。

[最小比較: G03](fix-md/README.md#g03) の `Selection[relation]: \Set` は、集合値の field `value: A` の射影を生成する際に `no product rule for these sorts` で失敗する。
現在は関係を parameter に持たない `Data: \Set` と、`Laws[relation, data]: \Prop` に分け、法則を満たすデータの部分集合型として `Selection` を定義することで型検査が通る。
`std.Set.FiniteSubset.Selection` ではこの構成を使っている。

> [!note]
> 保留します。
> 内容を見る限り G02 と同じ、 Prop をとって Set を返しているため。

<a id="g04"></a>

## G04: 子 module の macro 可視性と重複読み込み

実装方針は [macro のスコープと使用宣言](macro-scopes.md) にまとめる。

親 module で読み込んだ macro を子 module から利用するとき、読み込み位置と継承範囲を容易に把握したい。
同じ macro の再読み込みを許容できると、親と子のどちらから利用する場合にも import と `\use` を局所的に記述できる。

[最小比較: G04](fix-md/README.md#g04) では、親の `\use` が子の宣言より後にあると、子の展開時に `Named macro 'reflexive' is not visible` で失敗する。
子の宣言より前に移すと成功する。
一方、親で既に読み込んだ同じ macro を子で再び `\use` すると、`Macro 'reflexive' is already visible` で失敗する。
現在は子の宣言より前に親で読み込み、子では継承された macro を利用することで回避している。
`algebra.LaurentPolynomial` の `eq_reason` と `topology.Topology.Subspace` の `sym` で、それぞれこの問題を確認した。

> [!note]
> 対応したい。
> - マクロの利用範囲と宣言順...マクロを宣言順によらない依存を許す。
> - マクロの読み込みの挙動とオーバーライド...重複上書きあり、
> - ついでにマクロも `\import` にしたい。
> - `\import A[].{B[X := Y].b, c \as d}` みたいな書き方も。
> - マクロも使い分けのために `\as` が欲しいと思う。
> プランを決めたいが、いったん重複読み込みを許す。

<a id="g11"></a>

## G11: Machine の実行を Box にする定義

Machine を引数に取り、その実行を Box にする共通の定義を書きたい。
[最小比較: G11](fix-md/README.md#g11) は、Machine の引数で `Box requires a closed computation type` になり、具体値では成功する。
parameter と評価開始条件の検討は [Box の parameter](box-parameters.md#g11) にまとめる。

> [!note]
> 既知の問題のため、今は対処せず。

<a id="g12"></a>

## G12: 等しい次数間の集合値の移送

体系と処理系への追加は [等式による集合値の移送の実装プラン](equality-transport.md) にまとめる。

自然数の等式 \(k=l\) を用いて、`\idelim k = l \with m: Nat^ => Form m` と書いて形式を移送したい。
現在の等式除去は命題値の述語を要求するため、集合値の `Form m` をこの述語に置くことはできない。
外代数と局所形式は有限引数列のリスト表示に埋め込み、目的の次数で復元することで受け渡す。
[`Regrade`](../libs/differential_forms/src/Euclidean/On/Regrade.ref) は等式を明示的な構成引数として受け取り、埋め込んだ表示が保存されることと線形性を証明する。
次数の異なる表現を比較する結合則・次数付き可換則にも同じ表示を用いる。

<a id="g14"></a>

> [!note]
> 対応したい。
> `n + m = m + n` から `Form (n + m) -> Form (m + n)` が書けないとつらい。
> ただし、 reduction は行わない。
> agda のような、 `M1` と `M2` が definitional equivalence のときに `\idelim` が identity になることなど？
> 今は proof irr. なので問題ないようにも思えるが、まあ必要になったらでいいと思う。
> 本当か？ `f: (n, m: Nat) -> Form (n + m) -> Form (m + n)` に対して `f n (m + l) (f m l V) W = f ...` みたいな（順番は適当）をやりたいのでは？ 
> まあその場合は、 `\idelim n = m \with x: A => P \by { base: h, equality: p }` が n equiv m かつ h が refl の普通のやつでやればいいという説。
> でも今扱っている `=` は普通の equality じゃないからどうなのか...
> AI の助言: reduction じゃなくて普通に equality を提供する。
> 体系に refl がないのを忘れてたので、どうやっても refl かどうかを見ない（端点だけ見てる）形になりそう。
> \(\vdash \op{transport}(a, b, F, u): F b\) if \(\vDash a = b, \vdash u: F a\)
> \(\vdash \op{transport}(a, a, F, u) = u\) if \(\vDash u: F a\)
> 思い出したが、最初は全部 subset で書けると思っていたんだった。必要だわ。

## G14: signature の族に対する台集合の束ね直し

台集合を parameter に持つ任意の signature の族を受け取り、台集合を field に含めた signature と相互変換を共通の定義で構成したい。
たとえば、次の二つの構造の対応を、各構造の field を列挙せずに記述したい。

```text
\structure A[Carrier: \Set] { op1: Carrier, }
\structure ASet { Carrier: \Set, op1: Carrier, }
```

現在の signature は宣言された field の依存文脈へ展開され、signature の族そのものを parameter に取る仕組みがない。
sort が `\Set` の record の族なら、`F: \Set -> \Set` を受け取る signature に `Carrier: \Set` と `data: F Carrier` を持たせて汎用の相互変換を定義できる。
元の例と同じ field 配置を得るには、依存する field の型と本体を保って展開する仕組みも必要になる。

> [!note]
> 対応したい。
> すごいわかるため。
> A と ASet と ALaw と...を、一気に定義する方法があるべき。

## G15: 外延性の引数推論と存在証人を使う局所証明

座標の `decode` は商から降下した値の部分集合型を持つため、`decode (encode v)` を返す lambda の型推論は、通常の座標ベクトルより強い値域を返す。
その lambda と通常の引数列を直接 `funext` で比較すると、右辺にこの強い値域が要求された。
[`Pointwise.CoordinateRecovery`](../libs/differential_forms/src/Forms/On/Pointwise/CoordinateRecovery.ref) では、座標引数列を返す通常の定義 `roundtrip` に型を指定し、その外延性から復元の証明を構成する。

引き戻しの局所表示の等式を `Restricted.ext k _ _ (pointwise omega)` と書きたい。
点ごとの等式から二つの形式を推論する際に、形式を表す metavariable の等式が残り、宣言された等式との比較が失敗した。
[`Pullback.Between.Of.At.Local.law`](../libs/differential_forms/src/Pullback/Between/Of/At/Local.ref) では、制限した形式と引き戻した形式を明示して外延性を適用する。

局所一致から大域一致を示す際は、点を含む標的チャートを存在証明から取り出し、そのチャートでの等式を評価して返したい。
直接返す証明の推論型には、評価点の部分集合への埋め込みを通じて選んだチャートが残り、`\take map must have a non-dependent codomain` になった。
[`Pullback.Between.Of.At.localExt`](../libs/differential_forms/src/Pullback/Between/Of/At.ref) では、元の点での等式を型として指定した局所定義を介して返す。

閉形式の類へ等式を降ろす場合には、通常の形式の等式だけから `congr classOf _ _` の引数を推論すると、閉形式の部分集合への所属が保持されなかった。
[`PullbackComposition.Between.Of.At.cohomologyLaw`](../libs/differential_forms/src/PullbackComposition/Between/Of/At.ref) は、余鎖写像で得た二つの閉形式を明示し、形式の合成則から類の合成則を示す。

> [!note]
> 対応しません。
> `\as` で弱めればいいように思える。 `\of` だった。
