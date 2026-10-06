# 言語で書きたい構成と比較例

各項目の最小例と対照例は [比較サンプル一覧](fix-md/README.md#対象文書の対応) にまとめる。
リンク先の `.ref` は、全文を playground.md に貼り付けて単独で検査できる。
比較する条件と現在の結果は各項目のリンク先に記載する。
G11 の検討は [Box の parameter](box-parameters.md#g11) に分けている。

<a id="g01"></a>

## G01: record eta 則

record の変数 `s` と、各フィールドを射影して再構成した record を、定義的に等しいものとして扱いたい。

[最小比較: G01](fix-md/README.md#g01) は、変数と具体的な record に対して同じ等式を `refl` で検査する。
変数では `types are not convertible` で失敗し、具体値では成功する。

<a id="g02"></a>

> [!note]
> これは対応しなくていいかな。この gaps には残しておかないと、あとで同じものが記載されうるので残しておきます。

> [!note]
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい気がするので、保留する。

## G02: 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

[最小比較: G02](fix-md/README.md#g02) は、同じ証明引数と集合値について、通常の関数と contextual な定義を比較する。
通常の関数型 `P -> A` は sort の積規則で失敗し、contextual な `choose(h: P): A` は成功する。

<a id="g03"></a>

## G03: 関係を parameter に持つ record の集合値の射影

関係 `relation: A -> A -> \Prop` を Box parameter に持つ集合値の record に、データとその関係に関する法則をまとめたい。
有限選択の結果では、選択した有限集合と、元の集合との対応を表す法則を一つの record として扱いたい。

[最小比較: G03](fix-md/README.md#g03) の `Selection[relation]: \Set` は、集合値の field `value: A` の射影を生成する際に `no product rule for these sorts` で失敗する。
現在は関係を parameter に持たない `Data: \Set` と、`Laws[relation, data]: \Prop` に分け、法則を満たすデータの部分集合型として `Selection` を定義することで型検査が通る。
`std.Set.FiniteSubset.Selection` ではこの構成を使っている。

<a id="g04"></a>

## G04: 子 module の macro 可視性と重複読み込み

親 module で読み込んだ macro を子 module から利用するとき、読み込み位置と継承範囲を容易に把握したい。
同じ macro の再読み込みを許容できると、親と子のどちらから利用する場合にも import と `\use` を局所的に記述できる。

[最小比較: G04](fix-md/README.md#g04) では、親の `\use` が子の宣言より後にあると、子の展開時に `Named macro 'reflexive' is not visible` で失敗する。
子の宣言より前に移すと成功する。
一方、親で既に読み込んだ同じ macro を子で再び `\use` すると、`Macro 'reflexive' is already visible` で失敗する。
現在は子の宣言より前に親で読み込み、子では継承された macro を利用することで回避している。
`algebra.LaurentPolynomial` の `eq_reason` と `topology.Topology.Subspace` の `sym` で、それぞれこの問題を確認した。
