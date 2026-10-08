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

## G08: 点に依存する商の型と有限引数の関数型（修正済み）

多様体の各点 `x` の接空間を通常の型値の定義 `tangent M x` で返し、点ごとの交代形式の台集合を `\forall (x: M.Point) -> (Fin.Fin k -> tangent M x) -> Real` として公開したい。
[最小比較プロジェクト](reproductions/g08-pointwise-quotient/README.md)の全5例は、現在の処理系でキャッシュなしの検査に成功する。
修正前には直接の関数型や lambda の注釈で `uncaptured parameter` が出て、等式判定でも検査に失敗していた。

局所的な module 具体化で保持する束縛変数の型にだけ現れる module parameter が、kernel 登録時の capture に含まれていなかった。
定義の型・本体・明示的な引数に加え、局所文脈の束縛変数の型も依存として追跡することで解消した。
診断には元の module 名と capture 済みの引数も含め、同種の不整合の調査に利用できる。

```sh
python3 _plans/reproductions/g08-pointwise-quotient/check.py
target/debug/cli tests/projects/manifolds-de-rham --no-cache --diagnostics compact
```

[利用側の点ごとの API](../tests/projects/manifolds-de-rham/src/Pointwise.ref)では、商の型、有限引数列、二段階の外延性、恒等操作の等式証明を検査する。
[コホモロジーの利用例](../tests/projects/manifolds-de-rham/src/Cohomology.ref)では、次数に応じた部分加群の台集合と核の部分集合型の具体化を検査する。

## G09: 台集合に依存する位相と record 内の具体化

`Chart(M: \Set, space: topology.Topology[Carrier := M].Topology)` を通常の型値定義の局所引数で具体化したい。
この表現では、引数 `space` の推論型が `topology.Structures.Topology M` である一方、期待する classifier に元の `Chart` の module parameter が残り、型が一致しない診断が出た。
module parameter の classifier に `topology.Structures.Topology[M]` を直接使うことで回避できる。

多様体の record 内では、台集合 `Point` で具体化した namespace から Hausdorff 性と第二可算性の型を参照したい。
具体的な record の構築で `Failed to access item at path ... <temporary:17456>.Topology` が出る表現を確認した。
namespace での具体化を通常の命題値定義 `Hausdorff(M)(space)` と `SecondCountable(M)(space)` に移すことで回避できる。
チャート対の遷移写像を関数値として返す局所定義についても、対を scope に持つ `Atlas.Pair` を用いる表現へ整理した。
実装箇所は [位相多様体](../libs/manifolds/src/Dimension/Topological.ref)と[滑らかなアトラス](../libs/manifolds/src/Dimension/Atlas.ref)にある。

異なる次元の開集合間の連鎖律でも、`Multivariable[n := m].Open[].OpenSet` を module parameter の classifier に直接用いると、期待型に元の次元 parameter が残った。
`Real.OpenSpace(n)`、`OpenCarrier(n)(U)`、`ScalarFunction(n)(U)` を通常の型値定義として公開し、classifier と後続の依存する引数に用いることで回避した。
有限階微分の証人を lambda 内から具体化する際は、証人を固定する `Successor.Chosen` の子 module に移すことで、依存する族の型を保持できた。
任意次数の多重線形形式の基底展開でも、帰納法の中で `At[k := k].expandStep previous` を関数値として返す表現は kernel 登録時に `inferred: Set; expected: Nat` になった。
次数と直前の展開演算を自然な引数として固定する [`Finite.Expanded`](../libs/linear_algebra/src/Field/Space/Multilinear/Finite/Expanded.ref) に移し、復元公式と零次数を含めてキャッシュなしで検査した。
座標微分の外積を次数で帰納的に構成する場合も、`Step[k := k].value previous` の宣言引数付きの定義が同じ診断になった。
[`FiniteCoordinates.Exterior.Step`](../libs/linear_algebra/src/Field/Space/FiniteCoordinates/Exterior/Step.ref) では演算全体を関数型と lambda で定義し、零次数、増加添字上の双対性、有限和による復元までキャッシュなしで検査した。
整数次数の零拡張でも、帰納法の分岐の lambda 内で `Positive[n := n].apply` を参照すると、同じ `inferred: Set; expected: Nat` が出た。
実際の微分と部分集合の構築を分岐へ直接展開すると検査が通る。
具体的な複体で零拡張の `complex` をそのまま型注釈付きで返す場合は、加群の classifier に具体化前の環の parameter が残った。
[`Euclidean.On.DeRham`](../libs/differential_forms/src/Euclidean/On/DeRham.ref) は零拡張の台集合・演算・証明を使い、整数次数の `Family` と `Complex` を明示的に組み立てることで回避した。

有限置換の `Permutations.Step` の classifier でも、次元を変更した同じ module の `Permutation` を直接参照すると、親の次元が余分に適用された型として比較された。
同じ宣言の束の中に `PermutationType(k): Set` を通常の定義として置き、`Step(p: PermutationType (succ n))` として回避した。

恒等写像の引き戻しでも、lambda 内の `Differential[n := n, m := n].Between[M := M, N := M].At[f := f, x := x]` の classifier に、具体化前の次元が残った。
[`PullbackIdentity.On`](../libs/differential_forms/src/PullbackIdentity/On.ref) は、次元と多様体を固定した `Differential` と `DifferentialIdentity` を名前付き import にまとめ、点だけを局所的に具体化する。
微分同相による形式の同型でも、自己写像の引き戻しを [`PullbackDiffeomorphism.Between.Of`](../libs/differential_forms/src/PullbackDiffeomorphism/Between/Of.ref) にまとめ、同じ表現を利用する。
[`Restriction.On.To.apply`](../libs/differential_forms/src/Restriction/On/To.ref) では、宣言引数の次数を使って `Pullback.At[k := k].apply` をそのまま返すと、期待する形式の次数に次元が現れた。
次数と形式を関数型で量化し、lambda 内から引き戻しを適用することで回避する。

一般の次元で `Smooth.From.manifold` を経由して標準ユークリッド多様体を作り、その `smoothManifold` を二次元へ具体化した利用側でも、構造のフィールドに元の次元が残った。
最大アトラスの推論型は `Atlas(two)` である一方、フィールドの注釈には `Atlas(n, Point(n), space(n))` が残り、型注釈付きの構造の返却と滑らかな写像への引数の両方で失敗した。
[`Examples.Euclidean`](../libs/manifolds/src/Dimension/Examples/Euclidean.ref) と [`Examples.Empty`](../libs/manifolds/src/Dimension/Examples/Empty.ref) は、飽和したアトラスを持つ滑らかな多様体の構造を直接組み立てる。
[`Geometry`](../tests/projects/manifolds-de-rham/src/Geometry.ref) では、この表現による二次元の滑らかな多様体の返却と、標準多様体・空多様体の滑らかな恒等写像を検査する。

## G10: record の帰納法（修正済み）

record のフィールドから元の値を再構成する等式を、単一の constructor に対する帰納法で証明したい。
`\induction ... \with { | # : ... }` の分岐名を parser が identifier として受け取らず、elaborator も record を帰納法の対象として扱わなかった。
constructor `#` の分岐と record の通常の帰納法を実装した。
[型パラメータを持つ record の再構成](../tests/ok/system/record_induction.ref)と[有理数の列挙](../libs/std/src/Arithmetic/Rat/Enumeration.ref)で検査する。

法則を含む `\Set` の structure はデータ・法則・部分集合型へ展開されるため、公開された型に直接 `\induction` を適用してデータの constructor を指定することはできない。
[実数値線形写像](../libs/calculus/src/Real/Multivariable/Differential/Def.ref)は `LinearData` と `LinearLaws` を明示的に分け、通常のデータ record の帰納法から再構成の等式を示す。

## G11: 証明を引数に取る集合値の構成

滑らかな遷移写像の互換性から写像の値を作る構成を、`Compatible -> Maps.Map U V` の型と lambda で書きたい。
この型は `Prop` から `Set` への積になるため、現在の積規則では `no product rule` になる。
[`Atlas.Pair.smoothMap`](../libs/manifolds/src/Dimension/Atlas.ref) のように証明を宣言の明示的な引数へ移すと、同じ構成を記述できる。
小さいアトラスから滑らかな多様体を作る `Smooth.From.manifold` と、鳩の巣原理の証明で使う有限添字の縮小にもこの表現を適用している。
定理の仮定は命題全体の量化に含め、集合値を返す構成関数と区別する。

## G12: 等しい次数間の集合値の移送

自然数の等式 \(k=l\) を用いて、`\idelim k = l \with m: Nat^ => Form m` と書いて形式を移送したい。
現在の等式除去は命題値の述語を要求するため、集合値の `Form m` をこの述語に置くことはできない。
外代数と局所形式は有限引数列のリスト表示に埋め込み、目的の次数で復元することで受け渡す。
[`Regrade`](../libs/differential_forms/src/Euclidean/On/Regrade.ref) は等式を明示的な構成引数として受け取り、埋め込んだ表示が保存されることと線形性を証明する。
次数の異なる表現を比較する結合則・次数付き可換則にも同じ表示を用いる。

## G13: inline module から返す構造値（修正済み）

開部分多様体の構造を `OpenSubmanifold.On[M := M].In[U := domains i].manifold` から通常の定義として返したい。
構造値の解析が inline module の引数検査を保持するラッパーを扱わず、`definition does not satisfy structure result signature` になった。
ラッパー内の構造値を解析し、保持されているすべての引数検査を構造の検査へ渡すことで解消した。
同じ構造を使う貼り合わせの構成は [`Gluing.On.Cover.Piece`](../libs/differential_forms/src/Gluing/On/Cover/Piece.ref) にある。
処理系の回帰テストでは、型値とその値を持つ構造を直接返す構成と、誤った型の module 引数の拒否を検査する。

## G14: 具体化した定義を含む点依存の族の検査（修正済み）

接空間のベクトル空間や、`\fun (omega: Form k)(x: M.Point) => At[x := x].value omega` で点ごとの形式の族を定義したい。
検査済みの定義を具体化して参照すると、ソース位置に未解決変数を関連付ける探索が定義の証明本体まで展開し、メモリ上限に達した。
定義は検査時に閉じているため、未解決変数の探索は kernel の式を使い、定義参照の実引数をたどるよう修正した。
回帰テストでは、定義の本体が使わない実引数に含まれる未解決変数も検出し、ソース位置を保持することを確認する。

座標の `decode` は商から降下した値の部分集合型を持つため、`decode (encode v)` を返す lambda の型推論は、通常の座標ベクトルより強い値域を返す。
その lambda と通常の引数列を直接 `funext` で比較すると、右辺にこの強い値域が要求された。
[`Pointwise.CoordinateRecovery`](../libs/differential_forms/src/Forms/On/Pointwise/CoordinateRecovery.ref) では、座標引数列を返す通常の定義 `roundtrip` に型を指定し、その外延性から復元の証明を構成する。

## G15: 外延性の引数推論と存在証人を使う局所証明

引き戻しの局所表示の等式を `Restricted.ext k _ _ (pointwise omega)` と書きたい。
点ごとの等式から二つの形式を推論する際に、形式を表す metavariable の等式が残り、宣言された等式との比較が失敗した。
[`Pullback.Between.Of.At.Local.law`](../libs/differential_forms/src/Pullback/Between/Of/At/Local.ref) では、制限した形式と引き戻した形式を明示して外延性を適用する。

局所一致から大域一致を示す際は、点を含む標的チャートを存在証明から取り出し、そのチャートでの等式を評価して返したい。
直接返す証明の推論型には、評価点の部分集合への埋め込みを通じて選んだチャートが残り、`\take map must have a non-dependent codomain` になった。
[`Pullback.Between.Of.At.localExt`](../libs/differential_forms/src/Pullback/Between/Of/At.ref) では、元の点での等式を型として指定した局所定義を介して返す。

閉形式の類へ等式を降ろす場合には、通常の形式の等式だけから `congr classOf _ _` の引数を推論すると、閉形式の部分集合への所属が保持されなかった。
[`PullbackComposition.Between.Of.At.cohomologyLaw`](../libs/differential_forms/src/PullbackComposition/Between/Of/At.ref) は、余鎖写像で得た二つの閉形式を明示し、形式の合成則から類の合成則を示す。

<a id="g16"></a>

## G16: 構造を返す関数の依存するフィールド

添字 `i` で選ぶ開部分多様体を `manifold(i): Model.Manifold` として返し、別の添字 `j` で具体化した `(manifold j).Point` を使いたい。
構造のフィールドが具体化した module の定義を参照する場合、その module の引数に関数の宣言元の `i` が残り、`j` で選んだ点の型と一致しなかった。

[関数による構成](reproductions/g16-structure-family/function-result.ref) は、型族 `types: I -> Set` の `types i` をフィールドに持つ構造を返し、`types j` の値を `(bundle j).Carrier` として返す最小例である。
現在は `inferred: types j` に対して、期待型に `<definition:bundle>` の `i` が残り、`types are not convertible` になる。
[名前付き module による構成](reproductions/g16-structure-family/named-piece.ref) は、`At[i := j]` を import してから同じフィールドを参照し、検査に成功する。

```sh
target/debug/cli _plans/reproductions/g16-structure-family/function-result.ref --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g16-structure-family/named-piece.ref --no-cache --diagnostics compact
```

[`Gluing.On.Cover.Piece`](../libs/differential_forms/src/Gluing/On/Cover/Piece.ref) は、被覆の添字ごとに開部分多様体と形式の台集合をまとめる。
貼り合わせの各局所 module は開部分多様体を名前付き import で固定し、包含写像の微分と接空間にも同じ具体化を用いる。
