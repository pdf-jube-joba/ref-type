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

有限座標の零拡張でも、Bool の各分岐から等式の証明を受け取って成分を返す関数型が同じ制約に当たった。
`FiniteCoordinates.Tail.extension` は Kronecker delta の有限和で構成し、先頭の成分が零となることと制限写像との逆関係を命題として証明している。

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

> [!note]
> 対応したい。 visibility についてちゃんと考えるべき。
> - 自分のみ、子にも見える、このパッケージで見える、他のパッケージからも見える。
> - マクロの読み込みの挙動とオーバーライド、ついでに `\use A::{B, self}` みたいな書き方も。
> プランを決めたい。

<a id="g11"></a>

## G11: Machine の実行を Box にする定義

Machine を引数に取り、その実行を Box にする共通の定義を書きたい。
[最小比較: G11](fix-md/README.md#g11) は、Machine の引数で `Box requires a closed computation type` になり、具体値では成功する。
parameter と評価開始条件の検討は [Box の parameter](box-parameters.md#g11) にまとめる。

> [!note]
> 既知の問題のため、今は対処せず。

## G12: 等しい次数間の集合値の移送

自然数の等式 \(k=l\) を用いて、`\idelim k = l \with m: Nat^ => Form m` と書いて形式を移送したい。
現在の等式除去は命題値の述語を要求するため、集合値の `Form m` をこの述語に置くことはできない。
外代数と局所形式は有限引数列のリスト表示に埋め込み、目的の次数で復元することで受け渡す。
[`Regrade`](../libs/differential_forms/src/Euclidean/On/Regrade.ref) は等式を明示的な構成引数として受け取り、埋め込んだ表示が保存されることと線形性を証明する。
次数の異なる表現を比較する結合則・次数付き可換則にも同じ表示を用いる。

[`std.Set.Transport`](../libs/std/src/Set/Transport.ref) は集合値の道 `Path[a] b` の帰納法を使い、一般の型族に対する `cast` を提供する。
等式から道の存在を命題値の等式除去で示し、既存の古典的選択により道を選ぶ。
選択を正規化して道の一意性を証明するため、反射・逆移送・合成と自然性も得られる。
整数次数の鎖複体の直前の微分と次数反転は、この構成で受け渡す。
新しい公理を追加する必要はない。

<a id="g14"></a>

> [!note]
> 対応したい。
> `n + m = m + n` から `Form (n + m) -> Form (m + n)` が書けないとつらい。
> ただし、 reduction は行わない。
> axiom K のような、 `M1` と `M2` が definitional equivalence のときに `\idelim` が identity になることなど？
> 今は proof irr. なので問題ないようにも思えるが、まあ必要になったらでいいと思う。
> 本当か？ `f: (n, m: Nat) -> Form (n + m) -> Form (m + n)` に対して `f n (m + l) (f m l V) W = f ...` みたいな（順番は適当）をやりたいのでは？ 
> まあその場合は、 `\idelim n = m \with x: A => P \by { base: h, equality: p }` が n equiv m かつ h が refl の普通のやつでやればいいという説。
> でも今扱っている `=` は普通の equality じゃないからどうなのか...

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
> ちょっと後で考えたい。
> `\as` で弱めればいいように思える。

## G17: 型族の再帰と構造の段階的な具体化

自然数に沿って核を反復し、各段階の台集合と加群構造を一緒に返したい。
[`direct.ref`](reproductions/g17-type-families/direct.ref) の集合そのものを返す帰納法は `forbidden large elimination` になる。
[`wrapped.ref`](reproductions/g17-type-families/wrapped.ref) は台集合を `Set(1)` の構造に入れてから帰納法を行い、`Carrier` の型射影で型族を得る。
この比較例は検査に成功する。

加群構造も同じ構造の集合値のフィールドに入れると、[`space-field.ref`](reproductions/g17-type-families/space-field.ref) の射影 `space` の生成が `forbidden large elimination` になる。
[`continuation.ref`](reproductions/g17-type-families/continuation.ref) は構造の代わりに、任意の集合値の継続へ構造を渡す `spaceLift` を保持する。
台集合の型族を具体化した後に継続を使う `lower` は検査に成功する。
[`Module.Over.FreeResolution`](../libs/algebra/src/Module/Over/FreeResolution.ref) の任意加群の自由分解は、この方法で台集合と構造を組み立てる。

```sh
target/debug/cli _plans/reproductions/g17-type-families/direct.ref --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g17-type-families/wrapped.ref --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g17-type-families/space-field.ref --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g17-type-families/continuation.ref --no-cache --diagnostics compact
```

## G18: module の型引数を捕捉する実行用データ型の反映

実行用データ型を `Family(A: VType)` の中に宣言し、その反映上の帰納法を証明した後で `A` を具体化したい。
[`captured.ref`](reproductions/g18-native-captured-reflection/captured.ref) は、具体化した `reflexive` の検査で `parameter count mismatch`、`IndType`、`Lambda` を報告する。
型引数をデータ型自身の引数にした [`parameterized.ref`](reproductions/g18-native-captured-reflection/parameterized.ref) は検査に成功する。
[`std.Data.Nat.Iteration.Program`](../libs/std/src/Data/Nat/Iteration/Program.ref) は、親 module に宣言した `IterationState[A]` を使って反復の停止性と実行部の対応を具体化する。

```sh
target/debug/cli _plans/reproductions/g18-native-captured-reflection/captured.ref --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g18-native-captured-reflection/parameterized.ref --no-cache --diagnostics compact
```

## G19: 型を返す族の再公開と内部の module 参照

型を返す族を `Outer.family := Source.family` として再公開し、`Outer` の型引数を具体化した後に成分の型を取り出したい。
[`reexported.ref`](reproductions/g19-reexported-type-family/reexported.ref) は、族の成分が内部の `Slot[i := i]` を参照する最小例である。
再公開した名前空間から子 module を具体化するとき、元の宣言から現在の具体化先への対応を使って子の引数型を読み替えることで解消した。
直接参照・再公開参照の両方が検査に成功し、処理系の回帰テストでもこの依存を検査する。
[`reconstructed.ref`](reproductions/g19-reexported-type-family/reconstructed.ref) は族のフィールドを公開先で直接構成する別の書き方である。

```sh
target/debug/cli _plans/reproductions/g19-reexported-type-family/reexported.ref --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g19-reexported-type-family/reconstructed.ref --no-cache --diagnostics compact
```

## G20: 複体と依存する鎖写像を同じ module 呼び出しで渡す

複体と鎖写像を一度に具体化する次の宣言を使いたい。

```ref
\module Cone(C, D: Complex, f: \parent.Map[C := C, D := D].Map);
```

抽象的な複体 \(C\) に対し `Cone[C := C, D := C, f := End[C := C].identity]` を具体化すると、期待型の `D.family`・`D.differential` に `Cone` 自身の未具体化の引数が残る。
診断は `Module 'Cone' argument 'f' failed type checking: types are not convertible` であり、推論型の引数は \(C\) のフィールド、期待型の引数は \(C,D\) のフィールドになっている。
単純な台集合だけの構造や、族と微分だけの縮小例では検査に成功するため、複体のフィールドと準同型の法則を含む依存関係をさらに切り分ける必要がある。

[Chain.Over.Cone](../libs/homological_algebra/src/Chain/Over/Cone.ref) は複体を先に具体化し、`On[f := f]` で鎖写像を受け取る。
この形で任意の複体の恒等写像の cone、具体的な収縮、ホモロジー消滅を検査できる。
[BasicComplexes](../tests/projects/homological-algebra/src/BasicComplexes.ref) は整数加群に集中した複体への具体化も検査する。

## G21: 依存する構造フィールドの型と factory の具体化

構造を返す関数の引数で環境と台集合の族を具体化し、その戻り値を別の module から利用したい。
[`factory.ref`](reproductions/g21-nested-family-guards/factory.ref) は、複体の族に依存する分解データを構造のフィールドに持つ最小例である。
フィールドの型に保持された module 引数の検査が元の族を参照し、呼び出し元では存在しない `complex.family.Carrier` を読もうとしていた。
構造の各フィールドと捕捉した名前空間に引数の代入を適用し、解決中の親 module のパラメータも使って参照を具体化することで解消した。
添字を固定した族、フィールドの射影、型の別名、record の型引数と module 引数への適用を含む成功例、および異なる環境の族を渡す二つの拒否例を処理系の回帰テストで検査する。

## G22: 構造を引数に取る型の別名と捕捉した import

複体を引数に取る型の定義を、捕捉した `Chains` の import から `Chains.Pair[A := P, B := Q].Data` と書きたい。
[`imported.ref`](reproductions/g22-dependent-type-alias/imported.ref) は、factory の呼び出しで `A.family.space` の期待型に元の `Chains` の環境が残る例である。
[`explicit.ref`](reproductions/g22-dependent-type-alias/explicit.ref) は、型の定義内で `\root.Chains[R := R]` から参照し、環境の引数も具体化する書き方である。
`Resolution.Over.ShortExact.ChainSequence` はこの書き方で分解の短完全列を構成する。
