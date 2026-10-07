# 言語で書きたい構成と比較例

各項目の最小例と対照例は [比較サンプル一覧](fix-md/README.md#対象文書の対応) にまとめる。
G01〜G05 と G11 の `.ref` は、全文を playground.md に貼り付けて単独で検査できる。
G06 は依存ライブラリの具体化を検査するプロジェクトとして実行する。
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

## G02: 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

[最小比較: G02](fix-md/README.md#g02) は、同じ証明引数と集合値について、通常の関数と contextual な定義を比較する。
通常の関数型 `P -> A` は sort の積規則で失敗し、contextual な `choose(h: P): A` は成功する。

<a id="g03"></a>

> [!note]
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい気がするので、保留する。

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

<a id="g05"></a>

## G05: 式の中での module の具体化（修正済み）

依存するセルの次元を引数として `Euclidean.Dimension[n := dimension].Disk` のように台集合を参照したい。
[最小比較: G05](fix-md/README.md#g05) の `F.Dimension[A := A].Carrier` と、[実ライブラリの例](../tests/projects/module-expressions/src/Cells.ref) は検査に成功する。
関数の引数、lambda の束縛変数、record の先行 field を module 引数として、定義を参照できる。
macro の展開先でも宣言元の参照を保持し、package の読み込みとキャッシュの依存関係にも式中の module 参照を含める。

局所変数に依存する帰納型も具体化でき、同じ宣言と引数による型は一致する。

```text
\module Family(A: \Set) {
  \inductive Box: \Set := | box: A -> Box;
}
\definition box(A: \Set)(x: A): Family[A := A].Box :=
  Family[A := A].Box::box x;
```

帰納型の kernel 登録では元の宣言に module 引数を明示的に渡し、局所文脈を保持する。
record の field 射影と既定値にも同じ引数を引き継ぐ。

```text
\inductive Unit: \VType := | unit: Unit;
\module Value(A: \VType, x: A) { \definition value: A := x; }
\definition identity(x: Unit): \F(Unit) := \return Value[A := Unit, x := x].value;
```

Program の局所値は、引数検査と定義の登録まで局所文脈を引き継ぐ。
lambda、Program block、case branch、macro 内の束縛変数についても回帰テストで検査する。

<a id="g06"></a>

## G06: 積のコンパクト性定理の module 具体化（修正済み）

`topology.Product[A := I, B := K].Compactness` の `productCompact` を、集合を parameter に持つ別の module から通常の定理として利用したい。
修正前は元の `topology` パッケージを検査できても、定理の利用側でコンパクト被覆を表す有限集合の型が積空間の集合族として扱われず、`types are not convertible` で失敗していた。

[再現プロジェクト](reproductions/g06-product-compactness/src/Coordinates/Compactness.ref) は、二つの集合の位相と積の定理だけを読み込み、仮定を量化した同じ命題へ `productCompact` と `productCompactIn` を適用する。
キャッシュを使わず、リポジトリのルートから実行する。

```sh
target/debug/cli libs/topology --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g06-product-compactness --no-cache --diagnostics compact
```

現在は両方とも成功する。
修正前の利用側では、次の型の不一致が発生していた。

```text
inferred: std.Set.FiniteSubset[A := I, B := K].FiniteSubset(K, I)
expected: Pow(Pow(std.Data.Pair.Times^[I, K]))
```

原因は module 具体化時の参照の確定順序にあった。
型の比較で依存定義を実体化する際、積型の仮の ID がその定義に残り、後で確定した元の積型と異なる型として扱われていた。
parameter を持たない module の参照を先に確定することで修正し、再現プロジェクトを CLI の回帰テストに追加した。

<a id="g07"></a>

## G07: ホモトピー同値の反射の具体化（修正済み）

[Homotopy.ref の reflectedTwice](../tests/projects/topological-k-theory/src/Homotopy.ref) で、閉区間の反射を二回合成したホモトピー同値を構成したい。
次の検査は `reflectedTwice` を含めて成功する。

```sh
target/debug/cli tests/projects/topological-k-theory --no-cache --diagnostics compact
```

修正前は推論された位相が `Topology[A := Interval.Carrier, B := Interval.Carrier].Topology` である一方、期待型には `HomotopyEquivalence` の束縛変数 `B` による具体化が残り、`types are not convertible` になっていた。
G05 対応前の処理系でも同じ位置と診断で再現した。
検査済みの定義を保存するときに、依存先の参照と具体化した引数を保持することで解消した。

<a id="g08"></a>

## G08: 点に依存する商の型と有限引数の関数型

多様体の各点 `x` の接空間を通常の型値の定義 `tangent M x` で返し、点ごとの交代形式の台集合を `\forall (x: M.Point) -> (Fin.Fin k -> tangent M x) -> Real` として公開したい。

[最小比較プロジェクト](reproductions/g08-pointwise-quotient/README.md)は、点に依存する代表元の型と `std.Set.Quotient` の組合せまで縮小している。
直接の関数型による `sections` は `uncaptured parameter ModuleParamId { ... }` で失敗する。
通常の型値定義 `Function(A, B): Set := A -> B` を使った比較例は成功するが、同じ比較例に点・引数列ごとの等式判定を追加すると、`equal` で `expected Program value-type syntax` が出る。

点ごとの型を `At` module へ分ける比較例では、lambda の有限引数列を `Fin.Fin k -> fiber M x` で注釈すると `uncaptured parameter` で失敗し、`_` または `At.Arguments` を使うと成功する。
局所的な回避例も記録しており、構成全体の不可能性を示した結果ではない。

2026-10-07 に `a8498cb` の処理系で、全5例をキャッシュなしで検査した。
`uncaptured parameter` は lowering の capture 検査から返される診断で、修正箇所の特定は未完了である。

```sh
python3 _plans/reproductions/g08-pointwise-quotient/check.py
```

[多様体・De Rham 計画](manifolds-de-rham.md)の初期の表現検査で判明した処理系障害として、同計画の停止条件を適用した。
影響する構成は、第4節の点に依存する接空間と、第6節の点ごとの交代形式の解釈・等式判定である。
