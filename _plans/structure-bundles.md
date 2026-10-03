# 関連する宣言を束ねる structure

> [!note]
> `\Set` だろうと `\Prop` だろうと `\VType` だろうと、項も型（や型族）も関係なく詰め込めるレコードを作る。
> `\structure Name { field1: Type1, ...,}` で宣言して、 `Type1` のところにいろいろ入れられる形。
> この構造には sort がつけられなくなるが、 module と同様の名前解決と代入と思えば、基礎体系や kernel を変更しなくていい見込み。
> 例: `\structure Rel { A: \Set, R: A -> A -> \Prop }` これは `\inductive` でできるが、 `\Set` 値関数ではこれを使えない。
> 慎重に実装しないと、 kernel を迂回して (PropKind, Set) の impredicative を実装していることになって、普通に矛盾する。
> `\machine`, `\correspondenc`, `\record` は失くせる。
> `\definition` の引数では、 `(s: A)` で A が structure の場合を許すようにする。
> `\alias` は失くして `\definition` に入れる。

## 目的

`\structure` を、型・型族・述語・値・計算・証明・子 structure を一体にした宣言の束として扱う。
member の名前解決、依存関係、具体化、共有、構造間の変換を共通の仕組みにまとめる。
言語上の structure は独立した宣言として扱い、実装では module と束縛・置換・共有・文脈内検査の基盤を共用する。
各 member は、具体化された文脈で現行 kernel の判断と宣言登録を使って検査する。
関連型を保持するために束全体を PTS の項として表現する必要があるかは、値としての利用形態ごとに判断する。

代表的な利用対象は、同値関係と商、代数構造間の変換、Program 演算と数学側の仕様、停止性を備えた状態遷移である。
既存ライブラリの証明と実装を新しい宣言へ移し、利用側が通常の member 名で参照できる状態まで実装する。
現在の `\machine`、`\correspondence`、structure に付属する `\with` の用途は、共通の `\structure` と `\definition` に統合する。
`\alias` が担っている文脈内検査と具体化も `\definition` に統合し、名前付きの定義を共通の宣言規則で扱う。
field を持つ宣言は `\structure` に統一し、constructor を明示する宣言は `\inductive` で扱う。
既存の `\record` の依存する field、literal、projection の用途をこの二つの宣言へ移行する。


## 実装箇所

| 場所 | 役割 |
| --- | --- |
| `src/syntax/src/parse.rs`、`syntax.rs` | signature、既定値、sort、法則を保持した structure の AST |
| `src/resolve/src/structures.rs` | signature、束、宣言の文脈と束縛 ID による置換 |
| `src/resolve/src/structures/parameters.rs` | 入れ子の文脈展開、宣言引数の適合、部分具体化 |
| `src/resolve/src/structures/declarations.rs` | 抽象 field、既定値、定義を検査する module 文脈の構築 |
| `src/resolve/src/structures/normalization.rs` | field の具体化、全称量化、field 参照の source mapping |
| `src/resolve/src/representation.rs` | sort を持つ値のデータ・法則・refinement の生成 |
| `src/elaboration/src/elaborator/` | Set/Prop と Program の member 検査、product の形成、reflection |
| `src/elaboration/src/lowering/` | 文脈引数の構築と既存 kernel の宣言登録 |
| `src/sema/` | signature と field の semantic query、依存解析、schema 付きキャッシュ |
| `libs/std/src/Program.ref` | 実装と仕様、停止性を備えた状態遷移の共通 signature |
| `libs/std/src/Logic/Rel.ref` | 関連型を持つ関係、同値関係、商の束 |

sort を持つ structure のデータは単一 constructor の帰納型で表現する。
法則付きの値はデータと法則の refinement で表現する。
sort を持たない signature と具体化は front に保持し、各 member を検査済みの依存文脈と置換から展開する。
module の具体化と同じ置換・宣言 identity を使い、親 parameter と未使用 parameter も適合検査へ含める。

## 宣言モデル

### Module と structure の役割

module は parameter を受け取って具体化する名前空間であり、子 module も独自の parameter を持つ。
structure は依存する field の signature を定義し、その実装は signature を満たす一つの束として扱う。
structure 型の field の型には、子の signature に必要な parameter を具体化したものを指定する。
field の参照時には、その具体化を引き継いだ束の member を解決する。
parameter を受け取って structure の実装を作る操作は、外側の定義として表す。
signature 自体の parameter と、実装を作る定義の parameter を AST・HIR と型検査で区別する。

module と structure の構文、公開する semantic 情報、適合検査は、それぞれの意味に対応する宣言として保持する。
共通の内部表現は、束縛 ID、宣言への参照、依存文脈、置換、具体化した宣言の identity を扱う。
module の具体化と structure の field の具体化は、この共通処理をそれぞれの規則で利用する。

### Definition の signature と具体化

宣言の signature は、kernel の型、structure の signature、それらを引数・結果に持つ依存する宣言の signature を扱う。
`\definition` は、引数を宣言文脈に追加し、その文脈で本体が結果の signature を満たすことを検査する。
structure が引数または結果に現れる場合も、同じ適合検査と具体化の規則を使う。
定義への適用は、引数が要求された signature を満たすことを検査し、依存する引数と結果へ置換を適用する。
宣言文脈の member ごとに、kernel の文脈のもとで導出された項・型・計算を保持する。

名前付きの定義の引数と、項の中の lambda の引数を区別する。
lambda と kernel の関数適用は、既存の product rule で型検査する。
名前付きの定義は、検査済みの文脈と結果を持つ宣言として保持し、各 member を kernel の文脈付き定義または項へ展開する。
kernel の関数値として定義を利用する場合は、その signature を product 型として表現できることを検査して lambda を生成する。
部分適用と、定義自体を宣言の引数に渡す場合の signature・具体化も、この宣言規則で設計する。

既存の alias の引数、型、本体、参照は共通の definition に移行する。
移行前後で、文脈内の型検査、具体化後の項、依存する宣言の identity を確認する。

### Signature と実装

signature は要求する member の名前、カテゴリ、型、依存関係を持つ。
実装は signature の member に対する束縛と、既定の定義から作る member を持つ。
関連型・述語・Program 型を持つ signature は、まず宣言文脈として検査する。
次の例は構文案であり、最初の実装段階で parser と HIR の表現に合わせて確定する。

```text
\structure Relation {
  A: \Set,
  R: A -> A -> \Prop,
  reflexive: \forall (x: A) -> R x x,
  symmetric: \forall (x, y: A) -> R x y -> R y x,
  transitive: \forall (x, y, z: A) -> R x y -> R y z -> R x z,
}

\definition Equality(A: \Set): Relation := Relation {
  A := A,
  R := \fun (x, y: A) => x = y,
  reflexive := \fun (x: A) => \refl(x),
  symmetric := sym!{A},
  transitive := trans!{A},
};
```

member は宣言順の依存文脈を持ち、本体の検査に使う抽象 member と実装側の名前を束縛 ID で区別する。
例の `A := A` では左辺が signature の member、右辺が実装を作る定義の parameter を参照する。
`a: A` の `A` には structure の signature も指定できるようにする。
束の field も `a.member` で参照し、型位置の `a.A` と項位置の `a.value` を同じ名前解決で扱う。
structure を受け取る宣言では、束の parameter を依存する member の文脈へ展開し、呼び出し時に実引数の member を対応付ける。
その宣言の型と本体は展開後の文脈で検査し、関連型を含む引数への適用も共通の具体化として扱う。
field の型注釈には `\Set`、`\Prop`、`\VType` と、その文脈で形成できる型を使う。
`A -> A -> \Prop` のように型が Kind に分類される field も、member ごとの宣言カテゴリと既存の検査で扱う。
高階の型族を含む member も、その member の型と本体を宣言文脈で検査する。

### Structure 型の field と引数

```text
\structure Inner {
  A: \Set,
  R: A -> A -> \Prop,
}

\structure Outer {
  inner: Inner,
  element: inner.A,
}

\definition related(o: Outer): \Prop :=
  o.inner.R o.element o.element;
```

structure 型の field は、その signature を満たす束を保持する。
後続 field は、先行する束の field を型や述語として参照できる。
structure 型の引数と field は同じ宣言文脈の展開を使い、展開は入れ子に対して再帰的に行う。
利用側からは元の階層を持つ field 名で参照する。
親の member に依存する子の signature は、その依存を parameter として表し、子の field の型に具体化して使う。

```text
\structure RelationOn[A: \Set] {
  R: A -> A -> \Prop,
}

\structure WithRelation {
  A: \Set,
  inner: RelationOn[A],
  element: A,
}
```

親の実装で `A` と `inner` を束縛した時点で、子の signature の parameter と後続 field の型の対応を検査する。
`o.inner.R` は親の `A` に対する関係として解決する。
具体化の循環は依存グラフで検出し、循環に参加する member の source location を示す。

### Program の関連型

```text
\structure ProgramData {
  T: \VType,
  value: T,
}
```

`T` は Program value type の member、`value` はその型の Program value の member として検査する。
束の引数を展開するときも、Program の型・値・計算のカテゴリを保持する。
関連する Program 型は後続 field の型と reflection から参照できるようにする。
Program の文脈を構築し、既存の Program 型検査と reflection の規則で適合を検査する。

### 既定の定義と証明

signature の中で、必要な member と、先行 member から定義される member を区別する。
例えば加法と反数から減法を定義し、加法の法則から減法の性質を証明できるようにする。
既定の定義を上書きできる member と、その定義に依存する証明の扱いを明示する。
上書きにより前提となる定義が変わる場合は、依存する証明も新しい定義に対して検査する。
公開する定理の型には、必要な証明 member の前提を明示的に量化する。
束の具体化で供給された証明と、抽象的な前提を使う定理の区別を型と診断に残す。

### 共有と変換

束の一部の member を固定した部分具体化と、別の束の member をそのまま共有する具体化を扱う。
型の共有は束縛・宣言への参照として表し、型を通常の集合の要素とした等式証明へ置き換える前に名前と具体化の対応で解決する。
共有元の member の変更は、共有先の型と後続 member の検査に反映する。

構造間の変換は、変換先の signature に対する member の対応と定義として記述する。
例えば Group から Monoid を作るときは、台集合・単位元・演算・法則を元の構造から共有する。
Ring から加法モノイドを作る場合も、対応する演算と証明を選んで同じ仕組みで検査する。
変換の合成では共有した宣言 ID と具体化の対応を保持し、型や constructor が同じ由来を持つことを維持する。
変換先で新たに宣言した帰納型などは、その宣言の具体化として identity を管理する。

## 構造に対する量化と kernel 上の表現

`Topology` や `Monoid` は、現在のライブラリで全称量化や存在量化の対象として使われている。
宣言の引数として structure を受け取る場合と、kernel の命題の中で structure を量化する場合を区別する。
全称量化は、structure の依存する field を順に量化した式へ展開し、各段階の型形成と product rule を検査する。
存在量化は、既存の存在量化の規則に適合する証人の型と、束の field への対応を構築する。
全称量化と存在量化のそれぞれについて、展開後の判断と必要な表現を確認する。

kernel の型として表現できる structure には、既存の record の elaboration が生成する単一 constructor の帰納型と projection を利用する。
literal の field を constructor 引数に対応付け、通常の値の field 参照を projection に対応付ける。
nominal identity、依存する field の型、等式と帰納法の扱いを維持する。
固定された関連型・関連述語のもとで、データの型、法則の命題、法則付きの値の refinement を生成する現在の構成も利用する。
内部で生成した型と操作は、structure の member と source location に対応付ける。

関連する型や関係の member をどこまで値ごとに変えられるかは、生成する表現の分類と product rule に照らして検査する。
`\structure Packed: \SetKind` の表現を生成する場合と、固定 member と値の組み合わせで表現する場合を整理する。
生成が成立しない場合は、必要となった sort と product rule、および問題の member を診断する。
`a: A` による束の引数は宣言文脈への展開で扱う。
束を通常の関数値の引数に含める場合、束を返す通常の関数、型を隠した束の存在量化については、利用例と必要な kernel 表現を設計課題として整理する。

## 状態遷移と実装・仕様の対応

状態遷移は、`State`、`Output`、`step`、`terminates`、`run` を持つ共通の束として表す。
`run` の既定の定義は、検査済みの状態遷移と停止性証明から既存の実行項へ展開する。
実装と仕様の対応は、Program の型、`program`、`specification`、`coherence` を持つ束として表す。
Program の関連型の反映を後続 member から参照できるようにする。
reflection の型・停止性・閉性と、実装と仕様の等式を既存の kernel の規則で検査する。

ライブラリの共通 signature と既定の定義によって、現在の専用構文が生成している操作を表す。
状態遷移と実装・仕様の対応の宣言は、共通の `\structure` と、それを満たす実装を作る `\definition` に移行する。
生成される補助宣言と検証義務を明確にし、`Add.program`、`Add.specification`、`Add.coherence` のような member アクセスへ移行する。
データと証明は同じ signature の field とし、一つの structure literal の中で実装する。
現在の structure のデータ部分と `\with` の証明部分は、その field に対応付けて移行する。

## 検査と展開の責務

signature の検査、実装の適合検査、具体化後の member の検査をそれぞれ行う。
抽象 member の型と、その型に対して検査した本体を保持し、具体化の置換が型を保つことを文脈の構築と既存の kernel の検査で確認する。
型・述語・計算の各 member は、依存する文脈引数と具体化の置換として展開する。
既定の証明は実装ごとの具体化のもとで検査し、生成済みの検証義務も通常の宣言と同じ完了判定を通す。
未解決の推論変数、欠けた member、型の共有の不整合は、元の宣言と具体化箇所に対応する診断として返す。

kernel へ登録する項・宣言と、front に保持する signature・束の identity・source mapping の境界を実装前に文書化する。
module と structure に共通する具体化処理を独立した内部 API に整理し、structure の適合検査と field の展開をその上に実装する。
基礎体系への追加が必要になる利用形態は、必要な判断・sort・規則を具体例とともに記録する。
証明から集合値や集合そのものを構成する product rule の検討は、束の具体化に必要な規則と分けて整理する。

## 実装手順

### 1. 構文と文脈への展開を確定する

同値関係、型族を持つ構造、`\VType` を持つ構造、入れ子、共有、変換、通常の値表現の小さな例を用意する。
各例について、抽象 member の文脈、具体化の置換、検証義務、kernel へ渡す宣言を示す。
signature、実装、部分具体化、structure 型の field と引数、値表現の構文を確定する。
signature の parameter、実装を作る定義の parameter、field の型での具体化を区別し、子 module の具体化との対応を仕様にまとめる。
宣言の適用と kernel の関数適用の関係、部分適用、定義を宣言引数として受け取る場合を例と展開の対応表に含める。
この段階の成果物は、構文の仕様と、全例に対する展開の対応表とする。

### 2. AST・HIR と基本的な名前解決を実装する

structure を parser 内で完成済みの record 群へ変換する経路を、structure 自体を保持する AST と HIR に置き換える。
required member、既定の定義、structure 型の field と引数、member の具体化を共通の宣言モデルにする。
definition の signature に宣言の引数・結果を保持し、既存の alias の文脈付き定義を同じ表現へ統合する。
module と structure は別の宣言として保持し、共通の束縛・依存文脈・置換の表現を抽出する。
宣言の順序、親 scope の捕捉、名前の衝突、部分具体化の束縛を解決する。
型と関係を持つ束を具体化し、その member を参照できることを確認する。

### 3. 文脈内検査と具体化を実装する

宣言と module parameter の既存の文脈検査・置換処理を整理し、共通の member 検査から利用する。
module の具体化と structure の適合検査を別の入口に持ち、宣言 ID の対応付けと置換を共用する。
definition の適合検査と具体化を共通化し、通常の項・structure・宣言の各引数と結果を検査する。
kernel の関数値として使う箇所では、product 型の形成と lambda への変換を検査する。
Set/Prop、Program の値型・計算型・値・計算の各 member を適切な検査へ振り分ける。
入れ子の具体化と、既定の定義・証明の依存順を処理する。
関係を保持した商の束と、関連する Program 型を持つ演算の束を検証する。

### 4. 共有・変換・値表現を実装する

同じ member を共有する参照と、新しい member を定義する具体化を HIR と elaboration で区別する。
部分具体化、構造間の変換、その合成を実装する。
structure から単一 constructor の帰納型・projection と法則付きの refinement を生成し、通常の値から member を解決する経路を作る。
全称量化の field への展開と、存在量化の証人の表現を実装する。
Monoid と Group、Ring と Field、Topology と Product の利用例で、共有した台集合と演算の identity を確認する。

### 5. 実行と仕様の対応を共通の束へ移す

machine と correspondence の現在の展開を、ライブラリの共通 signature と既定の定義にまとめる。
データと法則を同じ signature に置き、structure に付属する `\with` の実装を一つの structure literal へ移す。
Bool の演算、Nat の反復、除算、GCD を移行する。
実行結果、停止性、reflection、仕様との一致が既存の kernel の検査を通ることを確認する。
呼び出し側の member アクセスを移行し、専用の生成名に依存している箇所を整理する。
移行した構文の parser・sugar・HIR・elaboration の専用処理を、共通の structure の処理へ統合する。

### 6. Semantic API とライブラリを移行する

宣言位置、参照、hover、診断に、元の member と具体化された member の対応を提供する。
signature、親 member、共有元、既定の定義の変更を incremental checker の依存関係に反映する。
永続キャッシュの表現変更に合わせて cache schema を更新し、再利用と再検査を確認する。
`libs/std`、`libs/real`、`libs/topology`、`libs/calculus` と利用例を移行する。
既存の alias の宣言と参照を definition へ移行し、構文・HIR・elaboration の専用処理を共通の定義処理へ統合する。
既存の record の宣言・literal・field 参照を structure へ移行し、constructor を明示して使う宣言は inductive へ移行する。
record の構文処理を統合し、帰納型・constructor・projection を生成する内部処理を structure と inductive から利用する。
構文の説明とライブラリの説明を更新し、`gaps.md` の要求と実装結果の対応を整理する。
ドキュメントと利用例の状態遷移・実装と仕様の対応・データと法則の宣言を、共通の structure の構文に揃える。

## 検証

signature と具体化のテストには、型・型族・命題値の関係・Program 型を持つ例を含める。
definition のテストには、structure を受け取り返す定義、部分適用、定義を宣言引数に渡す例、kernel の関数値として利用する例を含める。
既存の alias の利用例は definition として検証し、具体化後の項と依存する型の一致を確認する。
入れ子のテストには、親の型を使う子、複数段の具体化、部分具体化、共有した子の member の参照を含める。
parameter を持つ signature を field の型で具体化する例と、parameter を受け取る定義から入れ子の実装を作る例を含める。
共通の具体化処理の検証には、子 module が独自の parameter を持つ既存の利用例も含める。
変換のテストには、変換前後で同じ帰納型の constructor を使う例と、変換を合成した場合の型の共有を含める。
量化と値表現のテストには、任意の構造の値を受け取る定理と、構造の存在を証明する例を含める。
既存の record の利用例を structure として検証し、依存する field、literal、projection、Program の値、nominal identity を確認する。
constructor を明示する inductive への移行例では、constructor の適用と帰納法を確認する。
証明 member の型の不整合、共有した型の不整合、欠けた member、具体化の循環を検出し、該当する source location を確認する。
実行のテストには、Program の結果、停止性証明、反映後の仕様との一致を含める。
semantic query と cache のテストには、共有元と親 member を編集した際の再検査、無関係な束の再利用、キャッシュを使わない検査との一致を含める。

```sh
cargo run --quiet --bin cli -- libs/std --no-cache
cargo run --quiet --bin cli -- tests/projects/library --no-cache
cargo test --workspace
```

完了時には、代表例とライブラリ全体が共通の宣言モデルで検証でき、通常の値表現と入れ子・共有・変換の双方が利用できることを確認する。
現在の machine と correspondence の実行・証明の検証義務が、新しい member の定義として満たされることも確認する。
状態遷移、実装と仕様の対応、データと法則の実装が、共通の structure と definition の構文と検査経路を使うことを確認する。

## 実装結果

signature と field の具体化、入れ子、関連する Program 型、既定値と証明、構造間の変換を共通の文脈展開で扱う。
名前付き定義は通常の項と文脈付き定義を同じ構文で宣言し、structure を受け取り返す定義と部分適用も検査する。
定義を抽象引数として渡す signature は、member ごとの product 型に展開して形成を検査する。

通常の値、全称量化、存在量化には、それぞれ形成可能な kernel 表現を使う。
関連型を隠した束の存在量化には Set の証人の表現が必要であり、要求と必要な判断を `gaps.md` に記録した。
状態遷移の `run` はライブラリの既定値であり、具体化された実行の Box は既存の閉性検査を受ける。

Bool・Nat・Int、直積演算、除算、GCD、実数・位相・解析と利用例を共通の宣言へ移行した。
同値関係から商の束を作る利用例では、関連する台集合、関係、法則と商の演算の型の共有を検査する。
semantic query は元の signature と field の位置を保持し、signature の変更による再検査と永続キャッシュの再利用を検証する。

代表例は `tests/ok/declarations/signatures.ref` と `tests/projects/library/src/root.ref` にある。
不整合の検査には、既定値の上書き、未使用引数、親・signature の parameter、Kind の field 型注釈、形成できない callback の product 型を含む。

検証済みのコマンドは次のとおり。

```sh
cargo run --quiet --bin cli -- libs/std --no-cache
cargo run --quiet --bin cli -- tests/projects/library --no-cache
cargo test --workspace
```
