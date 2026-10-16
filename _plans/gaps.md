# 言語で書きたい構成と比較例

G02〜G05・G08・G09・G11・G13・G14 の比較サンプルは、全文を [playground](../extensions/playground/README.md) に貼り付けて単独で検査できる。
これらのサンプルを個別に CLI で確認する場合は、リポジトリのルートで実行する。

```sh
cargo build --locked --offline -p cli
target/debug/cli _plans/gaps/05-01-record-eta.ref --no-cache --diagnostics compact
```

Box の検討は [Box の parameter](features/box-parameters.md#g04) に分けている。

## 依存ライブラリを使う再現例

G10・G12 のサンプルは外部 package を import する module の本文である。
一時パッケージに配置し、共有キャッシュを使って実行する。

```sh
sample_dir=$(mktemp -d)
mkdir "$sample_dir/src"
printf '\\module Repro;\n' > "$sample_dir/src/root.ref"
cp _plans/gaps/10-02-total-direct.ref "$sample_dir/src/Repro.ref"
cat > "$sample_dir/ref.toml" <<EOF
[package]
name = "docgaps"
[dependencies]
std = { path = "$PWD/libs/std" }
module_theory = { path = "$PWD/libs/algebra/module_theory" }
double_complexes = { path = "$PWD/libs/algebra/homological/double_complexes" }
resolutions = { path = "$PWD/libs/algebra/homological/resolutions" }
EOF
target/debug/cli "$sample_dir" --module docgaps.Repro --cache-dir "$PWD/libs/refcache" --diagnostics compact
```

`cp` の入力を各サンプルに替えると、G10・G12 の四つの結果を比較できる。

<a id="g01"></a>

## G01: 外延性の引数推論と存在証人を使う局所証明

座標の `decode` は商から降下した値の部分集合型を持つため、`decode (encode v)` を返す lambda の型推論は、通常の座標ベクトルより強い値域を返す。
その lambda と通常の引数列を直接 `funext` で比較すると、右辺にこの強い値域が要求された。
[`Pointwise.CoordinateRecovery`](../libs/geometry/differential_forms/src/Forms/On/Pointwise/CoordinateRecovery.ref) では、座標引数列を返す通常の定義 `roundtrip` に型を指定し、その外延性から復元の証明を構成する。

引き戻しの局所表示の等式を `Restricted.ext k _ _ (pointwise omega)` と書きたい。
点ごとの等式から二つの形式を推論する際に、形式を表す metavariable の等式が残り、宣言された等式との比較が失敗した。
[`Pullback.Between.Of.At.Local.law`](../libs/geometry/differential_forms/src/Pullback/Between/Of/At/Local.ref) では、制限した形式と引き戻した形式を明示して外延性を適用する。

局所一致から大域一致を示す際は、点を含む標的チャートを存在証明から取り出し、そのチャートでの等式を評価して返したい。
直接返す証明の推論型には、評価点の部分集合への埋め込みを通じて選んだチャートが残り、`\take map must have a non-dependent codomain` になった。
[`Pullback.Between.Of.At.localExt`](../libs/geometry/differential_forms/src/Pullback/Between/Of/At.ref) では、元の点での等式を型として指定した局所定義を介して返す。

閉形式の類へ等式を降ろす場合には、通常の形式の等式だけから `congr classOf _ _` の引数を推論すると、閉形式の部分集合への所属が保持されなかった。
[`PullbackComposition.Between.Of.At.cohomologyLaw`](../libs/geometry/differential_forms/src/PullbackComposition/Between/Of/At.ref) は、余鎖写像で得た二つの閉形式を明示し、形式の合成則から類の合成則を示す。

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
| [02-01-proof-function.ref](gaps/02-01-proof-function.ref) | `choose: P -> A := \fun (h: P) => a`。 | 失敗：`no product rule for domain \Prop and body \Set(0)`。 |
| [02-02-proof-contextual.ref](gaps/02-02-proof-contextual.ref) | `choose(h: P): A := a`。 | 成功。 |

命題 `P`、集合 `A`、返す値 `a` は共通で、証明引数を通常の関数にするか contextual な定義にするかだけを変える。

滑らかな遷移写像の互換性から写像の値を作る構成を、`Compatible -> Maps.Map U V` の型と lambda で書きたい。
この型は `Prop` から `Set` への積になるため、現在の積規則では `no product rule` になる。
[`Atlas.Pair.smoothMap`](../libs/geometry/manifolds/src/Dimension/Atlas.ref) のように証明を宣言の明示的な引数へ移すと、同じ構成を記述できる。
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
| [03-01-relation-record.ref](gaps/03-01-relation-record.ref) | `Selection[relation]: \Set` に値と法則を保持する。 | 失敗：`Generated projection value does not typecheck: no product rule for domain \PropKind and body \Set(0)`。 |
| [03-02-relation-record-split.ref](gaps/03-02-relation-record-split.ref) | データと法則を分け、部分集合型で結ぶ。 | 成功。 |

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
| [04-01-box-machine.ref](gaps/04-01-box-machine.ref) | `machine` は定義の引数。 | 失敗：`Box requires a closed computation type`。 |
| [04-02-box-concrete.ref](gaps/04-02-box-concrete.ref) | `machine` は既に定義した具体値。 | 成功。 |

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
| [05-01-record-eta.ref](gaps/05-01-record-eta.ref) | `s` は定義の引数。 | 失敗：`types are not convertible`。 |
| [05-02-record-eta-concrete.ref](gaps/05-02-record-eta-concrete.ref) | `s` は既に定義した具体的な record。 | 成功。 |

差分は `eta` の `(s: Record)` の有無だけである。
両側とも `s = Record { field := s.field }` を `refl(s)` で検査する。
`refl` による定義的な eta の比較である。

法則を含む `\Set` の structure はデータ・法則・部分集合型へ展開されるため、公開された型に直接 `\induction` を適用してデータの constructor を指定することはできない。
[実数値線形写像](../libs/analysis/calculus/src/Real/Multivariable/Differential/Def.ref)は `LinearData` と `LinearLaws` を明示的に分け、通常のデータ record の帰納法から再構成の等式を示す。

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

<a id="g07"></a>

## G07: 存在導入の証人型の推論

宣言された存在命題と証人から、`\exact` の型引数を推論したい。
次の例は `constraint is not supported by the solver` で失敗する。

```text
\module Example(A: \Set, a: A) {
  \definition singleton: \exists { x: A \where x = a } :=
    \exact(\into[A](a, { x: A \where x = a }) \by { \refl(a) }, _);
}
```

型を明示すると同じ証明が通る。

```text
\module Example(A: \Set, a: A) {
  \definition singleton: \exists { x: A \where x = a } :=
    \exact(\into[A](a, { x: A \where x = a }) \by { \refl(a) },
      \Cast[A] ({ x: A \where x = a }));
}
```

ライブラリでは [Proposition.existsIntro](../libs/std/src/Logic/Proposition.ref) に部分集合への埋め込みと存在導入をまとめ、部分集合の条件を一度だけ指定している。

<a id="g08"></a>

## G08: signature parameter の型に使う構造の別名

構造の変換結果を通常の定義に名前付けし、その定義で具体化した signature を子 module の parameter 型に使いたい。
外部 module から、同じ変換式で具体化した signature の値を渡すときも、別名を展開して照合したい。

| サンプル | signature の具体化 | 結果 |
| --- | --- | --- |
| [08-01-signature-alias.ref](gaps/08-01-signature-alias.ref) | `Wrapper.ordinary := copied R p` を `Modules` の parameter に渡す。 | 失敗：`incompatible rigid expressions in metavariable constraint`。 |
| [08-02-signature-expanded.ref](gaps/08-02-signature-expanded.ref) | 同じ位置に `copied R p` を直接渡す。 | 成功。 |

各サンプルは23行であり、signature の構造、引数、変換式、利用側の import は同じである。
差分は `Wrapper` 内で `Modules` に渡す構造の別名を展開するかどうかである。
単なる record parameter の別名では同じ診断は再現せず、`Bundle` のように台集合とその台集合上の構造を持つ signature を渡す例で再現する。

`Tor.Over.ProjectiveSecond` から `resolutions.ResolutionTensor.Over.Of` を具体化した際、一般の可換環上の加群に対して、`Ring.commutativeRingAsRing R ring` と `ResolutionTensor.Over.ordinaryRing` の照合が同じ診断で停止した。
[ResolutionTensor.ref](../libs/algebra/homological/resolutions/src/ResolutionTensor.ref) では、依存 module の具体化へ変換式を直接渡すことで回避している。
この回避で射影係数による Tor の消滅を構成でき、一般の環への適用と巡回加群への具体化は型検査が通る。

<a id="g09"></a>

## G09: 構造を返す関数の結果からの入れ子の射影

構造の族 `terms: Index -> Complex` に対して `(terms i).family.Carrier` と書きたい。
[`09-01-structure-family-result.ref`](gaps/09-01-structure-family-result.ref) は、依存パッケージなしの7行の再現例で、`Item '<result>.family.Carrier' was not found` になる。
`#Carrier{#family{(terms i)}}` で明示的に射影しても同じ診断になる。

現在は対象の構造を parameter とする `View` module に射影を定義し、`View[C := terms i]` を import している。
[`09-02-structure-family-view.ref`](gaps/09-02-structure-family-view.ref) は、この書き方を14行で再現し、型検査を通る。
整数複体の直和では [`Chains.View`](../libs/algebra/homological/chain_complexes/src/Chain/Over/View.ref) を介して各複体の台集合・加群・微分を取り出す。

<a id="g10"></a>

## G10: total 複体の構造の別名の再公開

射影分解のテンソル total を `ResolutionTensor.Double.complex` から再公開したい。
[10-01-total-alias.ref](gaps/10-01-total-alias.ref) は `expected nested structure` で停止する。
[10-02-total-direct.ref](gaps/10-02-total-direct.ref) のように `DoubleComplex.Tensor` と `DoubleComplex.Total` を直接具体化すると、同じ複体を再公開できる。
`derived_functors.Tor.Balance` は後者を使う。
`Kunneth.Integer.Of.At.Component.torComplex` も、有限分解の Tor wrapper を経由せず `Tor.LengthOne.With` を直接具体化して再公開する。
各再現例は11行以内であり、一般の可換環、二つの加群、二つの非負鎖複体をすべて module parameter で束縛している。

<a id="g11"></a>

## G11: 子 module から親の値定義を直接参照する

親に定義した値を子から `\parent.value` と明示的に参照したい。
[11-01-parent-value.ref](gaps/11-01-parent-value.ref) は依存パッケージなしの6行の再現例で、`Module instantiation path must contain at least one module` になる。
[11-02-lexical-value.ref](gaps/11-02-lexical-value.ref) は同じ親の値を lexical scope の `value` として参照し、型検査が通る。
Tor の比較同型では、親の比較写像と同型に区別できる別名を付け、子のホモロジー module でこの別名を使っている。

<a id="g12"></a>

## G12: 台集合が変わる加群の族を自然数の帰納法で返す

零次に係数環、それ以外に零加群を置く族を、`Nat -> Modules.Bundle` の帰納法で定義したい。
[12-01-bundle-induction.ref](gaps/12-01-bundle-induction.ref) は11行の例で、`definition does not satisfy structure result signature` になる。
台集合を先に `Nat -> Set` の帰納法で定義する方法も、`forbidden large elimination` により使えない。

現在は階数だけを自然数の帰納法で定義し、各次数の加群を `FiniteCoordinates` の同じ構成で得る。
[12-02-coordinate-family.ref](gaps/12-02-coordinate-family.ref) は14行の例で、この形の族を公開する。
[`TensorCochain.Over.Unit`](../libs/algebra/homological/field_kunneth/src/TensorCochain/Over/Unit.ref) は階数を零次で一、そのほかで零とし、零次の唯一の座標での評価と定数一のベクトルを用いて左右の単位同型を証明する。

<a id="g13"></a>

## G13: module の引数に別の module の値を渡す

同じ header の先行 parameter を使って module の値を作り、その値を別の module の構造 parameter に渡して型を得たい。
[13-01-header-module-value.ref](gaps/13-01-header-module-value.ref) は依存パッケージなしの8行の例で、`unknown module expression scope` になる。
`Make[A, a].object` の台集合を `Use` を通して取り出すため、`Want` の最後の parameter は数学的には `A` の元である。

[13-02-header-reader.ref](gaps/13-02-header-reader.ref) は13行の例で、値を渡す処理を `Read` の本文へ移し、header からは公開した `Value: Set` を参照すると型検査が通る。
[`Kunneth.Field.Assertions.Maps`](../libs/algebra/homological/field_kunneth/src/Kunneth/Field/Assertions/Maps.ref) は有限複体の余鎖写像の型をこの形で公開し、自然性の定理の parameter に使う。

同じ制約は、関数の引数から作った値を別の module に渡す場合にも現れる。
[13-03-function-module-value.ref](gaps/13-03-function-module-value.ref) は引数から作った `Make[A,a].object` を `Use` に直接渡す8行の例で、同じ `unknown module expression scope` を再現する。
[13-04-function-reader.ref](gaps/13-04-function-reader.ref) は処理を `Read` の本文へ移す13行の回避例である。
整数 Künneth の `Theorem.SequenceAt` は次数ごとの短完全列の型を本文で組み立て、`Sequences(n)` はその公開型だけを読む。

<a id="g14"></a>

## G14: 部分集合の束縛変数から dot 記法で構造の field を読む

存在命題の部分集合 `{ s: Objects A \where s.value = a }` で、束縛変数 `s` の構造 field を dot 記法で参照したい。
[14-01-function-field.ref](gaps/14-01-function-field.ref) は5行の例で、`Module import 's' was not found` になる。
これは関数が返す型だけの問題ではなく、同じ部分集合の台を直接 `Object[A]` にした例でも再現する。

[14-02-explicit-projection.ref](gaps/14-02-explicit-projection.ref) は5行の回避例で、明示的な field projection `#value{s}` を使うと型検査が通る。
整数 Künneth の `Assertions.Exact` は `#inclusion{s}` を使って、外積が左端の写像である短完全列の存在を公開する。
