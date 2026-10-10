# 言語で書きたい構成と比較例

G02〜G05 の比較サンプルは、全文を playground.md に貼り付けて単独で検査できる。
個別に CLI で確認する場合は、リポジトリのルートで実行する。

```sh
cargo build --locked --offline -p cli
target/debug/cli _plans/fix-md/cases/05-01-record-eta.ref --no-cache --diagnostics compact
```

Box の検討は [Box の parameter](features/box-parameters.md#g04) に分けている。

<a id="g01"></a>

## G01: 外延性の引数推論と存在証人を使う局所証明

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

<a id="g02"></a>

> [!note]
> これは対応しなくていいかな。
> この gaps には残しておかないと、あとで同じものが記載されうるので残しておきます。

## G02: 命題を条件とする集合値の構成

命題の証明を引数に取り、集合値を返す関数を書きたい。
位相空間の正規性から得られる開集合や Urysohn 関数を、正規性の証明と閉集合の証明を引数とする集合値の関数として構成できると、存在証明を何度も展開せずに利用できる。

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [02-01-proof-function.ref](fix-md/cases/02-01-proof-function.ref) | `choose: P -> A := \fun (h: P) => a`。 | 失敗：`no product rule for these sorts`。 |
| [02-02-proof-contextual.ref](fix-md/cases/02-02-proof-contextual.ref) | `choose(h: P): A := a`。 | 成功。 |

命題 `P`、集合 `A`、返す値 `a` は共通で、証明引数を通常の関数にするか contextual な定義にするかだけを変える。

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

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [03-01-relation-record.ref](fix-md/cases/03-01-relation-record.ref) | `Selection[relation]: \Set` に値と法則を保持する。 | 失敗：`Generated projection value does not typecheck: no product rule for these sorts`。 |
| [03-02-relation-record-split.ref](fix-md/cases/03-02-relation-record-split.ref) | データと法則を分け、部分集合型で結ぶ。 | 成功。 |

保持する値と条件は共通で、record に関係 parameter を渡すか、法則を満たすデータの部分集合型を使うかを比較する。

現在は関係を parameter に持たない `Data: \Set` と、`Laws[relation, data]: \Prop` に分け、法則を満たすデータの部分集合型として `Selection` を定義することで型検査が通る。
`std.Set.FiniteSubset.Selection` ではこの構成を使っている。

> [!note]
> 保留します。
> 内容を見る限り G02 と同じ、 Prop をとって Set を返しているため。

<a id="g04"></a>

## G04: Machine の実行を Box にする定義

Machine を引数に取り、その実行を Box にする共通の定義を書きたい。

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [04-01-box-machine.ref](fix-md/cases/04-01-box-machine.ref) | `machine` は定義の引数。 | 失敗：`Box requires a closed computation type`。 |
| [04-02-box-concrete.ref](fix-md/cases/04-02-box-concrete.ref) | `machine` は既に定義した具体値。 | 成功。 |

差分は `runBox` の `(machine: Machine)` の有無だけである。
Machine の型、実行、Box の型と本体は共通で、Box の型は両側とも明示する。
入力と出力の型は1つの `State` にそろえている。
開いた computation type と、具体化して閉じた computation type の比較になる。
parameter と評価開始条件の検討は [Box の parameter](features/box-parameters.md#g04) にまとめる。

> [!note]
> 既知の問題のため、今は対処せず。

<a id="g05"></a>

## G05: record eta 則

record の変数 `s` と、各フィールドを射影して再構成した record を、定義的に等しいものとして扱いたい。

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [05-01-record-eta.ref](fix-md/cases/05-01-record-eta.ref) | `s` は定義の引数。 | 失敗：`types are not convertible`。 |
| [05-02-record-eta-concrete.ref](fix-md/cases/05-02-record-eta-concrete.ref) | `s` は既に定義した具体的な record。 | 成功。 |

差分は `eta` の `(s: Record)` の有無だけである。
両側とも `s = Record { field := s.field }` を `refl(s)` で検査する。
`refl` による定義的な eta の比較である。

法則を含む `\Set` の structure はデータ・法則・部分集合型へ展開されるため、公開された型に直接 `\induction` を適用してデータの constructor を指定することはできない。
[実数値線形写像](../libs/calculus/src/Real/Multivariable/Differential/Def.ref)は `LinearData` と `LinearLaws` を明示的に分け、通常のデータ record の帰納法から再構成の等式を示す。

<a id="g06"></a>

## G06: signature の族に対する台集合の束ね直し

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
