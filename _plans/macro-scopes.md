# macro のスコープと使用宣言

## 目的

[G04](gaps.md#g04) の可視性を、module 全体で確定する lexical scope として整理する。
macro の定義と使用宣言を宣言位置より前でも利用でき、親から継承する名前を子で上書きできるようにする。
使用宣言で定義元の module を具体化し、読み込み先の名前を指定できるようにする。
この文書は実装プランであり、以下の構文と検査結果は実装後の仕様を示す。

## 使用宣言

module の具体化には `\import` と同じパスと名前付き引数を使い、末尾の `::` で macro を選択する。
既存の import alias からも選択できる。
`\as` を省略したときの導入名は定義元の macro 名とする。

```text
\use \root.Equality[A := A, eq := leftEq, refl := leftRefl]::reflexive \as refl_left;
\use \root.Equality[A := A, eq := rightEq, refl := rightRefl]::reflexive \as refl_right;
\use \root.Templates[]::reflexive;
\use Eq::reflexive \as refl_eq;
\use Eq.Child[A := A]::reflexive \as refl_child;
```

`Eq` は `\import` で具体化した module の alias である。
直接具体化した module は使用宣言の内部に保持し、通常の module alias は `\import` で導入する。
現在の `\use Eq.reflexive;` は `\use Eq::reflexive;` に統一し、ライブラリ、サンプル、文書を移行する。
parameter の省略、型検査、structure 引数、親 module からの代入は `\import` の規則に従う。

## 可視性と名前の衝突

`\macro`、`\math-macro`、`\use` が導入する名前を、module ごとの一つの macro 名前空間に登録する。
導入名は本体全体と子 module に有効であり、使用宣言や macro 定義の前に書いた呼び出しにも適用する。
module のヘッダーと parameter の型は親の macro スコープで解決し、本体では自身の macro スコープを使う。

名前解決は自身から親へ進み、最初に見つかった導入名を採用する。
子の同名 macro は親の macro を隠し、子より前に書かれた親自身の式や兄弟 module の解決は、それぞれのスコープに従う。
子の上書きは子の本体全体に有効である。

同じ module 内で同じ導入名を二度登録した場合はエラーとする。
定義同士、定義と使用宣言、使用宣言同士を同じ規則で扱い、同じ具体化の同じ macro を再度読み込んだ場合も重複になる。
同じ定義元でも導入名が異なれば両方を読み込める。
診断には重複した導入名と両方の宣言位置を表示する。

名前付き macro は最寄りの導入名を一つ選び、その pattern と照合する。
選んだ macro の pattern が一致しない場合は、その呼び出しの不一致を報告する。

数式 macro も導入名による上書きを適用した後、残った候補を pattern で照合する。
候補の優先順位は、固定トークンの最左位置、呼び出しスコープからの距離、導入宣言のソース順とする。
最後の順序は resolver の実行順ではなく、各 module 内の宣言位置で固定する。
数式 macro の別名は導入名と衝突判定を変え、pattern の記号は定義元のものを使う。

`ModuleItem::Scoped` による宣言ブロックは既存の公開名と内部名の境界に従い、それぞれの有効なスコープ内で同じ規則を適用する。
生成された macro も、この境界と所属スコープを保持して登録する。

## 定義元と読み込み先の区別

macro の定義本体と、使用宣言が導入する binding を別のデータとして保持する。
binding は導入名、定義本体の ID、module の具体化、導入位置を持つ。
定義本体は定義元のスコープ、pattern、template、ソース位置を持つ。

template 内の macro 名は、定義元の完成した macro スコープで解決する。
後に定義・読み込みされた macro も参照できる。
別名で読み込んだ macro の内部参照と自己参照は、定義元で確定した ID を使う。
例えば `reflexive` を `refl_left` として読み込んでも、template 内の再帰呼び出しは同じ具体化の `reflexive` を指す。
子で同名 macro を定義した場合も、親で定義した template の内部参照は親のスコープに結び付く。
capture した式は呼び出し側で解決し、生成 binder の hygiene を保持する。

template 内の通常の項名は、macro の定義位置で利用できる名前に結び付ける。
使用宣言の module 引数も、その宣言位置で利用できる通常の項名と、その module の完成した macro スコープで解決する。
このため、スコープの収集と、通常の宣言・module 引数・template の解決を分離する。
同じ定義元を異なる module 引数で読み込んだ場合は、通常の項と内部 macro 呼び出しの両方に、その具体化の代入と module ID の対応を適用する。

## 依存関係と再帰

macro の定義・導入名、module 名、import alias の宣言位置を先に収集し、必要な定義元と具体化を依存関係に沿って解決する。
親の後続の使用宣言も、子の展開に先立って解決できるようにする。
本体が namespace だけの場合と通常の定義を含む場合に、同じ macro 可視性を適用する。

依存の対象には、module の解決、使用宣言の具体化、module 引数の展開、template の通常の項参照を含める。
宣言位置の項環境を保持し、必要な通常の宣言の処理を前提としてスケジュールする。
例えば子より後の使用宣言が、子より後かつ使用宣言より前の通常の定義を引数に取る場合、その定義を先に処理して使用宣言を解決する。
子からの通常の名前解決には、子の宣言位置に対応する項環境を使う。
module parameter の型と各宣言の検査順を含め、必要な依存を `CheckStep` に反映する。

依存ノードごとに未解決・解決中・解決済みを管理し、解決中のノードへ戻る具体化の依存は、経路と宣言位置を含む循環エラーにする。
使用宣言の引数の展開が、その使用宣言自身の具体化を要求する場合も、この循環に含まれる。

template 内の macro 呼び出しは定義収集時に参照先を結び付け、呼び出し時に展開する。
自己再帰と相互再帰を許容し、`\tmatch` の選択された枝だけを展開する。
既存の展開深さ上限 128 を維持し、展開が止まらない場合には macro の定義元と呼び出し位置を報告する。
template の呼び出し参照の循環と、具体化を完了できない依存の循環を区別する。

## Equality ごとの別名の例

以下は実装後に playground で単独検査する例である。
同じ `Equality` を二つの関係と反射律で具体化し、それぞれの導入名から対応する証明を得る。
macro の使用宣言と定義元の module は、呼び出しより後に置いている。

```text
\module Consumer(
  A: \Set, a: A,
  leftEq: A -> A -> \Prop, leftRefl: \forall (x: A) -> leftEq x x,
  rightEq: A -> A -> \Prop, rightRefl: \forall (x: A) -> rightEq x x
) {
  \module Child {
    \definition leftProof: leftEq a a := refl_left!{a};
    \definition rightProof: rightEq a a := refl_right!{a};
  }
  \use \root.Equality[A := A, eq := leftEq, refl := leftRefl]::reflexive \as refl_left;
  \use \root.Equality[A := A, eq := rightEq, refl := rightRefl]::reflexive \as refl_right;
}
\module Equality(A: \Set, eq: A -> A -> \Prop, refl: \forall (x: A) -> eq x x) {
  \macro reflexive($x) := refl $x;
}
```

現在の構文では、具体化のための import と、同名 macro の導入を分けるための子 module を用意する。

```text
\module Equality(A: \Set, eq: A -> A -> \Prop, refl: \forall (x: A) -> eq x x) {
  \macro reflexive($x) := refl $x;
}
\module Consumer(
  A: \Set, a: A,
  leftEq: A -> A -> \Prop, leftRefl: \forall (x: A) -> leftEq x x,
  rightEq: A -> A -> \Prop, rightRefl: \forall (x: A) -> rightEq x x
) {
  \module Left {
    \import \root.Equality[A := A, eq := leftEq, refl := leftRefl] \as Eq;
    \use Eq.reflexive;
    \definition proof: leftEq a a := reflexive!{a};
  }
  \module Right {
    \import \root.Equality[A := A, eq := rightEq, refl := rightRefl] \as Eq;
    \use Eq.reflexive;
    \definition proof: rightEq a a := reflexive!{a};
  }
}
```

## 実装手順

1. `src/syntax` の使用宣言を、module 選択、macro 名、任意の導入名を持つ AST に変更する。
   `\import` と module パスの parser を共通化し、visit、lower、HIR、宣言位置の情報を更新する。
2. `src/resolve` に macro 定義 ID と導入 binding を設け、スコープごとの名前収集、ローカル重複検査、親の名前の遮蔽を実装する。
   通常の項環境の宣言位置と macro の完成したスコープを別々に保持する。
3. module、import、macro 使用宣言、通常の宣言の前提を解決する状態管理を実装する。
   `resolver.rs` の本体走査と namespace 特例を整理し、子を処理する前に必要な親の macro binding を確定できるようにする。
4. 直接の使用宣言に既存の module 引数の解決・検査・具体化を再利用する。
   内部の具体化を elaboration に渡し、`CheckStep` と module ID・binding ID の対応を更新する。
5. template の内部 macro 参照を定義元の ID に結び付け、具体化時に参照先の環境も対応させる。
   `max_order` による可視性制限を完成したスコープの参照に置き換え、数式候補の順序をソース位置から決める。
6. 通常の macro と、`scoped.rs` や structure 正規化が生成する macro を同じ登録経路で扱う。
   参照記録、定義位置への移動、診断、LSP と playground の情報を更新する。
7. リポジトリ全体の `\use`、macro 文書、関連テストを新しい構文と可視性へ移行する。
   G04 の比較例と結果を更新し、下記の検証を完了する。

## 検証と完了条件

- 呼び出しより後の定義・使用宣言、後方の定義元 module、親の後続の使用宣言を検査する。
- 親・子・孫の上書き、兄弟の独立性、親で定義した template の内部参照の固定を検査する。
- 同じスコープ内の定義同士、定義と使用宣言、使用宣言同士の重複と、異なる別名による共存を検査する。
- 二つの具体化を同時に読み込み、それぞれの関係の証明が得られることを型検査する。
- 直接の module パス、既存 alias、parameter を持つ子 module、structure 引数、親からの代入を検査する。
- 別名で読み込んだ自己再帰、後方参照を含む相互再帰、選択された `\tmatch` の枝、展開上限を検査する。
- module 引数と使用宣言の循環、通常の項への依存を含むスケジュール、循環診断の経路を検査する。
- 数式 macro の同名遮蔽と、異名で同じ pattern を持つ候補の優先順位を検査する。
- 宣言ブロック、生成 macro、module parameter の型、source reference の位置を検査する。

`cargo test --locked --offline --workspace` と既存のライブラリ検査を実行する。
G04 の親の後続の読み込みは成功し、親と子での同名読み込みも子の binding として成功する。
同じ module 内の重複はエラーとなり、二つの Equality の具体化は別名で同時に利用できる。
その結果を G04 の文書に反映した時点で実装完了とする。

macro の具体化とスコープ解決の結果はプロジェクトの検査キャッシュで再利用する。
キャッシュの識別には、定義元、具体化引数、導入名、内部参照と親の有効な macro 環境を含め、診断と候補選択はキャッシュの有無にかかわらず一致させる。
性能確認が必要な場合は、小さい入力と測定手順を `benchmarks/` に置く。
