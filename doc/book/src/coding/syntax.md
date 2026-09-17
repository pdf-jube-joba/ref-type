# 表面構文

この文書は、現在の front のパーサーが受理する `.ref` の表面構文をまとめたリファレンスである。
コード例中の `expression`、`type`、`value`、`computation` などは、それぞれ該当する式で置き換える。

## 字句

空白、タブ、改行、フォームフィードはトークンの間で無視される。
コメントは `/* ... */` で、入れ子にできる。

```text
/* outer /* nested */ outer */
```

識別子は英字で始まり、続きに英数字と `_` を使える。大文字と小文字は区別される。
キーワードは `\definition` のように `\` と英字で始まり、その後に英数字と `-` を使える。

数値は十進の非負整数で、現在は sort level と番号付き metavariable に使う。
文字列状のマクロトークンは改行を含まない `"..."` である。エスケープシーケンスはない。

記号列は可能な限り一つのトークンになる。隣接する二つの記号トークンを意図する場合は空白で
区切る。次の記号には構文上の意味がある。

```text
( ) \( \) { } [ ]
^ | : ; . , = ! ::
-> ~> <- => :=
```

## ファイルと module

通常のルートファイルには一つ以上の module を置く。

```text
\module Name(parameters) {
  module-items
}

\module Empty {}
```

`parameters` は後述する通常の注釈束縛をコンマで並べる。括弧そのものと末尾のコンマは省略できる。

```text
\module Example(A, B: \Set, x: A, P: A -> \Prop) { ... }
```

本体を別ファイルに置く module は `;` で宣言する。

```text
\module Algebra(A: \Set);
```

ルートファイルと同じディレクトリの `Algebra.ref` には、外側の `\module Algebra { ... }` を
書かず module item を直接置く。外部 child module のパスも module の入れ子に対応する。

module は入れ子にできる。module item は宣言順に処理される。

### import

module の instance 化と alias の導入には `\import` を使う。

```text
\import CurrentChild[A := T, x := value] \as C;
\import \parent.Sibling[] \as S;
\import \parent.\parent.Outer[] \as O;
\import \root.Top[A := T] \as T0;
\import \root.Top[A := T].Nested[] \as N;
\import ExistingAlias.Child[x := value] \as Child;
```

module path の各要素は `Name[name := expression, ...]` と書く。parameter のない module にも
`[]` が要る。引数名、個数、順序は宣言と一致させる。`\root.` はルートから、`\parent.` は
一つ外側の module から探索する。先頭が既存の import alias と `.` の組なら、その instance を
親として child module を instance 化する。

module argument は通常の式構文を使うが、metavariable の推論は行われない。

## 宣言

### 定義

```text
\definition name: type := expression;
\definition name(x, y: A)(z: B): type := expression;
```

名前の後の束縛は複数グループ書ける。Set/Prop の定義では通常の関数束縛、Program の
computation 定義では `~>` と `\cfun` に相当する糖衣になる。型と本体から Set/Prop、Program
value、Program computation のどの定義かを判定する。

型関連 item は owner を `::` の前に書く。

```text
\definition Type(parameters)::item(arguments): type := expression;
```

例は `\definition List(A: \VType)::head(xs: List[A]): \F(A) := ...;` である。
owner parameter は owner の型 parameter に対応する。
引数付きの Program computation 定義は、たとえば
`\definition f(x: A, y: B): C := body;` なら型 `A ~> B ~> C` と本体
`\cfun (x: A) (y: B) => body` に展開される。

### 帰納型

```text
\inductive Type(parameters): result-kind :=
| constructor1: constructor-type;
| constructor2: constructor-type;
;
```

`result-kind` は `\Prop`、`\PropKind`、`\Set`、`\SetKind` または `\VType` である。
constructor がなくても、宣言全体を閉じる最後の `;` は要る。

```text
\inductive Nat: \Set :=
| zero: Nat;
| succ: Nat -> Nat;
;

\inductive List(A: \VType): \VType :=
| nil: List;
| cons: A -> List[A] -> List;
;
```

constructor は `Type[parameters]::constructor arguments` で参照する。Program constructor の
field type は value type であり、`->` は constructor field を区切る構文としても使われる。

### structure

```text
\structure Type(parameters): result-kind := {
  field1: type1,
  field2: type2,
};
```

field の末尾のコンマは任意で、空の `{}` も使える。Set/Prop structure の field は前の field に
依存できる。Program structure の kind は `\VType` で、field は非依存の value type である。

値の構築には `\record` を使う。

```text
\record Type[parameters] { field1 := value1, field2 := value2 }
\record Empty {}
```

record literal の末尾のコンマは任意である。projection は `Type[parameters]::field record` と書く。
Program projection は computation で、結果を値として使うには `\bind` する。
record literal の field 順は任意だが、宣言された全 field を一度ずつ指定する。

### 検査・実行 item

Set/Prop 式に対する item は次のとおり。

```text
\check expression: type;
\infer expression;
\eval expression;
\normalize expression;
```

Program は judgement ごとに item が分かれる。

```text
\vcheck value: value-type;
\vinfer value;
\ccheck computation: computation-type;
\cinfer computation;
\ceval computation;
\cnormalize computation;
```

`eval` 系は評価、`normalize` 系は正規化を表示する。

## 束縛、名前、metavariable

通常の注釈束縛は次の形である。同じ型の名前をコンマでまとめられ、束縛リストの末尾のコンマも
許される。束縛位置の `_` は匿名名である。

```text
(x: A)
(x, y: A, z: B)
(_: A)
```

式位置では `_`、`?`、`?N` が metavariable になる。

- `_` は制約から一意に補完する implicit hole。
- `?` は出現ごとに新しい goal。
- `?0`、`?12` などは同じ elaboration 単位の同じ番号どうしで共有する goal。

匿名名 `_` は注釈束縛、式形式の `\let` と `\bind`、block の `\bind` で使える。
block の `\let` と `\match` branch の field 名には通常の識別子を書く。

名前の参照は次の形を持つ。

```text
name
Import.name
Type[A, B]::item
Import.Type[A, B]::item
```

`[...]` は型や定義の位置 parameter で、空にもできる。`Import.name` のような local access は
一段の import alias を持つ。`::` は constructor、projection、型関連定義に共通であり、式に対して
左結合で繰り返すこともできる。

Program の datatype、constructor、record literal、型関連 item では、型 parameter をすべて省略した
形や `_` で指定した形を周囲の型から推論できる。決まらない parameter は goal または ambiguity に
なる。

Program の名前に `^` を付けると Set 側への reflection を明示する。

```text
Bool^                  /* reflected datatype */
Bool^::true            /* reflected constructor */
Wrap^[Bool^]           /* reflected parameterized datatype */
value^                 /* reflected Program value */
identity^              /* reflected Program definition */
M.Bool^
M.value^
```

`^` は access path の末尾に付く独立したトークンである。Program module parameter も同様に
`A^`、`a^` として参照できる。

## 式の共通構造と優先順位

任意の式は `(expression)` で囲める。通常の関数適用は空白で並べ、左結合する。
等号は一度だけ書ける。矢印は右結合する。

```text
f x y
x = y
A -> B -> C
A ~> B ~> C
```

強い順の優先順位は次のとおり。

| 構文 | 結合 |
| --- | --- |
| atom と `(expression)` | — |
| `expression::item` | 左 |
| `function argument` | 左 |
| `left = right` | 連鎖不可 |
| `A -> B`、`A ~> C` | 右、同順位 |

`\let` と `\bind` は最も外側の binding form として、`\in` の後を式の右端まで読む。
`\return` も後続の value 式全体を読む。一方 `\thunk` と `\force` は直後の postfix atom
だけを取るため、複合 computation/value を包むときは括弧を使う。
binding form を関数の引数に置く場合にも括弧を使う。

```text
\return f x
\thunk (f x)
\force suspended
(\force suspended) x
```

## Set/Prop の式

### sort と関数

sort は次の四系列である。Set 系は level を省略すると 0 になる。

```text
\Prop
\PropKind
\Set
\Set(2)
\SetKind
\SetKind(2)
```

非依存関数、依存積、lambda は次のように書く。

```text
A -> B
\forall (x: A) -> B
\forall (x, y: A) (z: B) -> C
\fun (x: A) => body
\fun (x, y: A) (z: B) => body
```

refinement binder は `\where` で条件を、任意の `\as` でその証明の束縛名を与える。
`\where` を使う場合は値の束縛名を一つだけ書く。

```text
\forall (x: A \where P x) -> B
\fun (x: A \where P x \as proof) => body
```

### powerset、subset、存在

```text
\Power(A)
\Subset(x, A, predicate)
\Ty(A, subset)
\Pred(A, subset, element)
\subsetinto(A, subset, element, membership-proof)
```

`\Subset` は `A` 上の subset、`\Ty` はその refinement type、`\Pred` は membership、
`\subsetinto` は membership proof を伴う refinement value を作る。

存在と choice は次の形である。

```text
\exists A
\exists {x: A \where P x}

\take (x: A) => body
\by { existence: existence-proof }

\take (x: A) => body
\by { existence: existence-proof, uniqueness: uniqueness-proof }
```

`uniqueness` がない形は proposition-valued choice、ある形は set-valued choiceになる。
field 名と順序は固定である。

### 等号と証明項

```text
left = right
\refl(element)
\exact(element, set)
\bysub(superset, subset, element)
```

`\exact` は存在の導入、`\bysub` は refinement value から membership proof を取り出す。
等号消去は次の形である。

```text
\idelim(left = right \with x: A => predicate)
\by (base, equality)
```

choice の結果に関する等号は次で作る。

```text
\takeelim(function, element, domain, codomain)
\by (existence, uniqueness)
```

組み込み公理は三つある。

```text
\axiom:setext(left, right, left-to-right, right-to-left)
\axiom:funext(left, right, pointwise)
\axiom:classicalIndefiniteChoice(domain, family, inhabited)
```

### 帰納型の消去

通常の eliminator は branch 名と branch 項を並べる。

```text
\elim scrutinee \in Type \return motive {
| constructor1 => branch1
| constructor2 => branch2
}
```

import や reflection を使う型なら `\in M.Type`、`\in Type^` と書ける。branch の末尾に
`;` は付けない。

primitive recursor は次の atom を作り、その後ろに motive と constructor ごとの branch を
通常の関数適用として渡す。

```text
\prec(sort, Type[parameters]) motive branch1 branch2
```

`sort` は四つの PTS sort のいずれかである。

### 論理ブロック

```text
\block {
  \fix (x, y: A), (h: P x);
  \let z: B := term;
  \enough C \by map;
  \return result;
}
```

ブロックは 0 個以上の `\fix`、`\let`、`\enough` 文と、必須の最後の `\return` からなる。
`\fix` は現在の目標の前方から引数を固定する。異なる型の binder group は `,` でつなぐ。
論理側の `\let` は局所定義で、後続の項と型では定義内容まで展開できる。

最終目標が `B` のとき、`\enough A \by map;` は `map: A -> B` を使い、残りのブロックの
目標を `A` に変える。各文が導入した名前は後続だけで有効で、注釈と右辺は導入前の scope で
解釈する。

## Program

Program は CBPV に従い、value type、computation type、value、computation を区別する。

### 型

```text
\VType             /* value type の sort */
\F(A)              /* A を返す computation type */
\U(C)              /* C の thunk である value type */
A ~> C             /* value A を受け取る computation function type */
\RunStep(A, B)     /* run の一ステップを表す value type */
```

`\F` の引数は value type、`\U` の引数は computation type、`~>` の左辺は value type、右辺は
computation type として分類する。

`A -> B` は call-by-value の糖衣でもある。computation type の位置では `A ~> \F(B)`、value
type の位置では `\U(A ~> \F(B))` として読む。定義の型に裸で書いた `A -> B` は computation
type を優先するため、関数 value の型は `\U(A -> B)` と明示する。この矢印に依存束縛や
refinement は書けない。

### value と computation

基本形は次のとおり。

```text
\return value
\thunk computation-atom
\force value-atom
\cfun (x: A) => computation
function value
```

computation application の引数は value である。computation の結果を引数に渡す場合は先に
`\bind` する。`\thunk` と `\force` の複合引数には括弧を付ける。

Program の文脈では `\fun` と `->` も CBV の糖衣として使える。`\fun` は computation 位置で
`\cfun`、value 位置ではさらに `\thunk` で包まれる。複数引数の `\fun` は後続の関数を
`\return (\thunk ...)` で返す。最後の本体は computation なので `\return` は明示する。

```text
\definition identity(x: A): \F(A) := \return x;
\definition suspended: \U(A ~> \F(A)) := \thunk identity;
\definition curried: A -> B -> C :=
  \fun (x: A) (y: B) => \return result;
```

### 局所束縛と Program ブロック

式としての束縛は次の形で、型注釈は必須である。

```text
\let x: A := value \in computation
\bind y: B <- computation1 \in computation2
```

`\let` は value、`\bind` は computation の結果を束縛する。`_` を束縛名として結果を捨てられる。
名前は `\in` より後だけで有効であり、型注釈と右辺は外側の scope で解釈する。

同じ構造を文として並べられる。

```text
\program {
  \let x: A := value;
  \bind y: B <- computation;
  \return result;
}
```

Program block で使える中間文は `\let` と `\bind` だけで、最後の `\return value;` は value を
返す computation に展開される。

### Program の場合分け

```text
\match scrutinee \in Datatype \with {
| constructor1 => computation1
| constructor2 field1 field2 => computation2
}
```

scrutinee は value、branch の field は value として束縛され、branch body は computation である。
datatype 名は必須で、parameter はここでは書かない。branch は次の `|` または `}` で終わり、
末尾に `;` は付けない。これは完全な非再帰 case analysis である。

## 一般再帰と reflection

### RunStep と accessibility

一ステップの値は次で作る。

```text
\continue(state-type, result-type, next-state)
\finish(state-type, result-type, output)
```

Set 側には同じ形の reflected `\RunStep` と、停止性を表す次の項がある。

```text
\Acc(state-type, result-type, step, state)
\accintro(state-type, result-type, step, state, predecessors)
\accdescent(state-type, result-type, step, from, to, accessibility, transition)
```

`RunStep` の recursor は次の六引数である。

```text
\runStepRec(state-type, result-type, motive, on-continue, on-finish, scrutinee)
```

### run

```text
\run(state-type, result-type, step, initial) \by accessibility
```

`step` は thunk された Program step function、`accessibility` は Set reflection 上の停止性証明で
ある。既に一回分の transition computation を持つ形もある。

```text
\runCase(state-type, result-type, step, initial, transition)
\by (accessibility, transition-equality)
```

### Box

Program computation と Set 項の間の reflection には次を使う。

```text
\Box(program-computation-type)
\box(program-computation-type, computation)
\Force(program-computation-type, boxed)
\boxapp(boxed-function, boxed-argument)
```

value を box に入れる場合は `\F(A)` と `\return value` を使う。`\boxapp` は box の中の
Program function application を表す。

## マクロ

マクロには数式マクロと名前付きマクロがあり、どちらも module item として宣言する。

```text
\math-macro name(pattern) := template;
\macro name(pattern) := template;
```

同じ module または親 module の可視なマクロは直接使える。import したマクロは明示的に導入する。

```text
\use ImportAlias.macroName;
```

### pattern

pattern atom はコンマで区切る。

| pattern | 意味 |
| --- | --- |
| `$name` | 通常の式を一つ捕捉する |
| `name` | 記号または引用トークンを一つ捕捉する |
| `..name` | 残りの列を 0 個以上捕捉する |
| `\+` など | `\` を除いた固定の記号トークンに一致する |
| `"tag"` | 固定の引用トークンに一致する |
| `(pattern, ...)` | 入れ子の列に一致する |

`..name` は各 pattern 列の末尾に一つだけ置ける。構文予約された記号は固定マクロトークンには
使えない。数式マクロで使える capture は `$name` だけで、bare `name` と `..name` は名前付き
マクロ専用である。

template では `$name` で式 capture、bare `name` で token capture、`..name` で残りの列を
展開する。template 中の自由な通常名はマクロ定義側、capture した式は呼出側の scope で解決する。

### 呼び出し

数式マクロは `\( ... \)`、名前付きマクロは `name!{ ... }` で呼ぶ。名前と `!` は隣接させる。
呼出側の列はコンマではなく、空白またはトークン境界で atom を並べる。

```text
\(x + y \)
choose!{x "+" y}
```

マクロ列内の `( ... )` は通常式の括弧ではなく、常に入れ子のマクロ列になる。複合した通常式を
一つの式 capture に渡すには `{ expression }` と書く。その内側では通常の式構文に戻る。

```text
\((x + y) + { f (g z) } \)
tagged!{{ f x } "keep"}
```

数式マクロは各括弧階層の列全体に一致する。内側の列を先に展開し、候補が複数なら最も左に
固定トークンを持つもの、その中では宣言順が早いものを選ぶ。

### template 内の token match

名前付きマクロの template では token capture または rest capture を分岐できる。

```text
\tmatch capturedName {
| \+ => expression
| "+" => expression
| ($head, ..tail) => expression
| () => expression
| _ => default-expression
}
```

pattern は固定記号、固定引用トークン、入れ子の pattern 列、または `_` である。branch は上から
最初に一致したものを使う。空の branch 集合も書け、網羅性は静的には要求されない。
branch 内の capture はその branch body だけで有効である。

名前付きマクロは自分自身を呼べる。それ以外の template 内呼び出しから見えるのは、それ以前に
宣言されていたマクロである。展開深さの上限は 128 である。

## 構文一覧

式を導入する現在のキーワードは次のとおりである。

```text
\Prop \PropKind \Set \SetKind
\VType \U \F
\fun \forall \cfun
\return \thunk \force \let \bind
\Power \Subset \Pred \Ty \subsetinto
\exists \take
\exact \bysub \refl \idelim \takeelim \axiom
\elim \prec
\record \match
\block \program
\RunStep \continue \finish \Acc \accintro \accdescent
\run \runCase \runStepRec
\Box \box \Force \boxapp
\tmatch
```

module item を導入する現在のキーワードは次のとおりである。

```text
\module \import \definition \inductive \structure
\math-macro \macro \use
\check \infer \eval \normalize
\vcheck \vinfer \ccheck \cinfer \ceval \cnormalize
```

`\as`、`\by`、`\in`、`\with`、`\where`、`\root`、`\parent`、block 内の `\fix` と
`\enough` は、それぞれ上記の複合構文内で使う。

実行方法と診断については [利用方法](../../../../src/USAGE.md) を参照する。
