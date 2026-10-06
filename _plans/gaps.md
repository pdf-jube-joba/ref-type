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

## G02: 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

[最小比較: G02](fix-md/README.md#g02) は、同じ証明引数と集合値について、通常の関数と contextual な定義を比較する。
通常の関数型 `P -> A` は sort の積規則で失敗し、contextual な `choose(h: P): A` は成功する。

<a id="g03"></a>

> [!note]
> 矛盾しなさそうなのは言われているんですが、こういう Prop -> Set はちょっと許しがたい気がするので、保留する。

## G03: 宣言された型からの証明引数の推論

証明の引数の型を、定義の宣言された型から推論して record の射影や存在証明の消去に使いたい。

対応済み。
[最小比較: G03](fix-md/README.md#g03) は、射影、存在消去の証人と継続、部分集合の元について、同じ定義の型注釈だけを `_` と明示型で切り替える。
全例が成功する。

<a id="g04"></a>

> [!note]
> 対応したい。

## G04: 定義した型名からの帰納型の操作

`\definition` で名前を付けた帰納型に対して、その名前で constructor の参照と帰納法を書きたい。

対応済み。
[最小比較: G04](fix-md/README.md#g04) は、constructor の参照名と帰納法の対象型を、それぞれ定義した名前と元の帰納型名で切り替える。
両方成功する。

<a id="g05"></a>

> [!note]
> 対応したい。

## G05: モジュール引数に依存する部分集合型の商

区間に依存する部分集合型を、汎用の商モジュールの台集合として渡したい。

[最小比較: G05](fix-md/README.md#g05) は、部分集合の条件が外側のモジュール引数に依存するかだけを変える。
商を恒等関数に縮めた組と、商の構成を残した組があり、どちらも引数に依存する場合に失敗する。
具体化済みの `Representation` と、具体化前の定義への参照が残る型が convertible と判定されない。

[外側の引数を内部 import に渡す比較](fix-md/cases/05-05-forward-context.ref)では、`Pass` に未使用の `u: Unit` を追加し、`u := u` を渡すと成功する。
G06 と同じ、具体化時の宣言 ID の置き換えと既存定義の再利用の順序に関係する症状と考えられる。

<a id="g06"></a>

## G06: 具体化したモジュール内の型と座標空間

体を parameter に取るモジュールの中で有限添字型を宣言し、その型を座標空間や基底の添字に使いたい。

[最小比較: G06](fix-md/README.md#g06) は、座標空間の操作を恒等関数に縮め、内部 import の関数を使うか、添字型を内部で宣言するかを別々に比較する。
内部の帰納型を内部 import の関数に渡す場合に失敗する。
具体化済みの `Outer.Unit` と元の `Outer.Unit` が convertible と判定されない。

原因は、内部 import の定義を再利用するか判定する時点で、外側の宣言 ID の置き換え表が未完成なことである。
`bind_namespace_from` は内部 import を外側の宣言より先に処理し、`reserve_lazy_definition` は未置換の `Outer.Unit` を引数として既存の `Pass.identity` を再利用する。
後で `Outer.Unit` の新しい ID を割り当てても、再利用された定義は再具体化されない。
[外側の引数を内部 import に渡す比較](fix-md/cases/06-04-forward-context.ref)では、`Pass` に未使用の `K: \Set` を追加し、`K := K` を渡して具体化の引数を変えると成功する。

<a id="g07"></a>

## G07: 圏の signature を添字に取る Set の構造

対象の集合と射の集合族を持つ圏を、そのまま関手の構造の添字に使いたい。

[最小比較: G07](fix-md/README.md#g07) は、signature を Set のフィールド1つまで縮め、同じ構造の実引数を signature 全体と展開済みのフィールドで切り替える。
signature 全体を渡す場合に、実引数のアクセスで失敗する。

sort を指定しない `\structure A[Carrier: \Set]` と `\structure ALaw[Carrier: \Set, data: A[Carrier]]` を定義し、別の structure の field に `data: A[Carrier], law: ALaw[Carrier, data]` と書きたい。
現在は `ALaw` の parameter が field ごとに展開され、`ALaw[Carrier, data]` では引数の個数が一致せず、`name does not denote a Program value type: 'Carrier'` で失敗する。
`A` の field が `unit, op, inv` の場合、`ALaw[Carrier, data.unit, data.op, data.inv]` と展開して渡すと成功する。
`A` に sort `: \Set` を指定した record では、`ALaw[Carrier, data]` のまま成功する。

<a id="g08"></a>

## G08: contextual な定義をモジュール引数に渡す

証明内の型を推論させた関手の定義を、モジュール引数に直接渡したい。

[最小比較: G08](fix-md/README.md#g08) は、signature を取る恒等関数まで縮め、lambda の型注釈と、検査済みの定義名を渡すことの影響を別々に比較する。
`_` を含む contextual な定義を直接渡すと `module arguments do not allow inference holes` で失敗する。
型注釈を明示する場合と、先に型注釈付きの定義を検査してその名前を渡す場合は成功する。

<a id="g09"></a>

## G09: ブロックで導入した contextual な関手の射影

関手を証明ブロックの中で導入し、その対象写像を使いたい。

[最小比較: G09](fix-md/README.md#g09) は、関手をフィールド1つの record に縮め、射影の記法と lambda の位置を別々に比較する。
ブロック内で導入した変数の `x.field` は `Module import 'x' was not found` で失敗する。
`x #field` にする場合と、lambda をブロックの外へ置く場合は成功する。

原因は、局所変数の束縛処理より前に行う `normalize_structures` が、通常のブロック内の `\fun` と `\let` で局所スコープを更新しないことである。
この段階で `x.field` を射影に変換できず、後続の名前解決が `x` をモジュールの import 名として扱う。
[`\let` の比較](fix-md/cases/09-04-block-let.ref)でも `y.field` は同じ理由で失敗し、[`y #field`](fix-md/cases/09-05-block-let-hash.ref)は成功する。

<a id="g10"></a>

## G10: 集合値関手の内部で具体化した自然変換の型

集合値関手のモジュール内で、表現可能関手からの自然変換の型を既存のモジュールから取得したい。

[最小比較: G10](fix-md/README.md#g10) は、自己関数を射とする圏に限定し、自然変換型を内部 import する場合と同じ型を内部で定義する場合を比較する。
自然性と、具体化後の `evaluateFromElement` の等式は共通で、両方成功する。
過去に報告した `Unit` と `C.Object` の不一致は、この比較では再現していない。

<a id="g12"></a>

## G12: 帰納型の再帰的な述語

帰納法で命題や述語を再帰的に定義したい。

対応済み。
[最小比較: G12](fix-md/README.md#g12) は、述語族、命題、冪集合について、同じ述語の再帰定義と非再帰の定数関数を比較する。
定義の検査と、同じ入力に対する簡約の検査が両方成功する。

<a id="g13"></a>

## G13: parameter を持つ帰納型の match

parameter を持つ List の要素を、Set 側でも直接場合分けしたい。

対応済み。
[最小比較: G13](fix-md/README.md#g13) は、同じ要素型を使い、List 自身に parameter を持たせる場合と持たせない場合を比較する。
constructor、結果型、match の枝は共通で、両方成功する。

<a id="g14"></a>

## G14: 引数付きの算術定義を一致性証明で使う

自然数の算術関数を `\definition isZero(n: Nat^): B.Bool^ := ...` のように宣言ヘッダで引数を取る定義として書き、import 先の一致性証明でも合同則の暗黙引数を推論させたい。
[Basic.Def](../libs/std/src/Data/Nat/Basic/Def.ref) の算術関数をこの形式に変更すると、[Parity.ProgramProp](../libs/std/src/Data/Nat/Parity/ProgramProp.ref) の `EvenProof.matches` で `occurs check failed` と暗黙 metavariable の矛盾が発生した。
同じ関数を `\definition isZero: Nat^ -> B.Bool^ := \fun (n: Nat^) => ...` の形式で定義すると、一致性証明を含む標準ライブラリ全体の検査が成功する。
