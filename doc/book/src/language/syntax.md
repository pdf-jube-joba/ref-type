# 表面構文

現在の `.ref` ファイルで使われている表面構文を、目的別にまとめる。
例中の `<...>` は実際の名前や式に置き換えるメタ記号である。

目的別の入口:

- [字句と共通記法](#1-字句と共通記法)
- [module](#2-module) / [宣言](#3-宣言)
- [式の共通構文](#4-式の共通構文)
- [Set/Prop](#5-setprop) / [Program](#6-program-cbpv)
- [一般再帰・Run・Box](#7-一般再帰runbox) / [マクロ](#8-マクロ)

目的別の入口:

- [字句・名前・metavariable](#1-字句と共通記法)
- [module と import](#2-module)
- [宣言](#3-宣言)
- [式の優先順位](#4-式の共通構文)
- [Set/Prop](#5-setprop)
- [Program](#6-program-cbpv)
- [再帰・Box](#7-一般再帰runbox)
- [マクロ](#8-マクロ)

## 1. 字句と共通記法

### 字句

- 空白、タブ、改行、フォームフィードは区切りとして無視する。
- `/* ... */` は入れ子可能なコメントである。
- 識別子は英字で始まり、英数字と `_` が続く。
- キーワードは `\name` の形式で、名前には英数字と `-` が使える。
- 数値は十進の非負整数である。
- `"..."` は改行を含まない引用マクロトークンである。エスケープはない。

次の記号は構文トークンである。

```text
( ) \( \) { } [ ]
^ | : ; . , = ! ::
-> ~> <- => :=
```

その他の記号列は一つのマクロトークンになる。別々の記号トークンを隣接させる場合は空白で
区切る。

### parameter と名前

型、alias、constructor、型関連 item、module の引数は角括弧で指定する。空の `[]` も指定できる。

```text
Type[A, B]
Type[A, B]::item argument
\import my_package.M[A := T, x := value] \as Alias;
\import my_package.M[] \as Alias;
```

名前へのアクセスは `.` と `::` を使う。

```text
name
Import.name
Type[A]::item
Import.Type[A]::item
```

Program の名前の末尾に `^` を付けると Set 側への reflection になる。

```text
Bool^
Bool^::true
Wrap^[Bool^]
value^
identity^
Import.Bool^
Import.value^
Pair[Bool]::first^
Pair[Bool]::#^
```

Program の datatype、constructor、record literal、型関連 item の parameter は、文脈から決まる場合に省略または `_` で指定できる。

### metavariable

| 表記 | 意味 |
| --- | --- |
| `_` | 出現ごとに作る推論変数 |
| `_0`、`_1` | 同じ宣言の型注釈と本体で番号を共有する推論変数 |
| `?` | 期待型と文脈を調べるための hole |

推論変数は制約から解決する。
共有する推論変数の解は、各出現に共通する外側の binder に依存できる。
束縛名の `_` は匿名名である。

Set/Prop の式には `\assign` で番号付き推論変数との等式を登録できる。
式を elaboration した時点で制約を解き、同じ宣言の型注釈と本体で共有する。
式の値は左辺のままで、既に解がある場合は整合性を検査する。
`\assign` の結合順位は矢印より弱い。

```ref
\definition andAssoc (P, Q, R: \Prop):
  PropEquiv[And[And[P, Q], R] \assign _1, And[P, And[Q, R]] \assign _2] :=
  PropEquiv[_1, _2] {
    lt := \fun (h: _1) => And[_, _]::# (h #left #left) (And[_, _]::# (h #left #right) (h #right)),
    rt := \fun (h: _2) => And[_, _]::# (And[_, _]::# (h #left) (h #right #left)) (h #right #right),
  };
```

`?` がある module の elaboration は失敗し、その位置の期待型、ローカル変数、関連する制約を報告する。
制約から項が求まった場合も hole を報告し、求まった項を表示する。
同じ宣言に未解決の推論変数がある場合は、それらも一緒に表示する。

診断では、情報不足、他の metavariable の解待ち、solver が扱えない制約、制約の矛盾を区別する。
制約にはソース上の metavariable の番号、発生位置、解決前後の式を表示する。

## 2. module

ルートファイルには module を一つ以上置く。module は入れ子にでき、item は宣言順に処理する。

```text
\module Name(parameters) {
  <module-item>*
}

\module Name(parameters);
```

`;` で終わる宣言は外部 module である。対応する `Name.ref` には外側の module 宣言を書かず、
module item だけを置く。子 module のファイルパスは module の入れ子に対応する。

### import

```text
\import .Child[A := T] \as C;
\import \parent.Sibling[] \as S;
\import \parent.\parent.Outer[] \as O;
\import my_package.Top[A := T] \as T;
\import my_package.Top[A := T].Nested[] \as N;
\import ExistingAlias.Child[x := value] \as Child;
```

各 path 要素は `Name[arg := expression, ...]` で書き、parameter の個数・名前・順序を宣言と一致させる。先頭の `.` は現在の module から、パッケージ名はそのパッケージのルートから、`\parent.` は一つ上の module から探索する。
既存 alias から child module を instance 化するときは `Alias.Child[...]` と書く。
module argument では metavariable の推論を行わない。

## 3. 宣言

### definition

```text
\definition name: type := expression;
\definition name(x, y: A)(z: B): type := expression;
\definition Type(parameters)::item(arguments): type := expression;
```

括弧付き binder は複数 group 書ける。型と本体から Set/Prop、Program value、Program computation のいずれかに分類される。`Type::item` は型関連 item で、owner の parameter を先頭に束縛した定義になる。

Program computation 定義の引数は CBV の糖衣である。

```text
\definition f(x: A, y: B): C := body;
/* A ~> B ~> C と \cfun (x: A) (y: B) => body に相当 */
```

### alias

```text
\alias Relation[Carrier: \Set]: \PropKind := Carrier -> Carrier -> \Prop;
\alias At[A: \Set, x: A, P: A -> \Prop]: \Prop := P x;

\definition reflexive(A: \Set)(r: Relation[A]): \Prop :=
  \forall (x: A) -> r x x;
\definition atSelf(A: \Set)(x: A): At[_, x, \fun (y: A) => x = y] :=
  \refl(x);
```

alias は Set/Prop の式に名前を付ける宣言である。
宣言時に parameter の文脈で本体を検査し、使用時に各引数を検査して本体へ代入する。
import した alias は `M.Relation[A]` のように参照する。

### inductive

```text
\inductive Type[parameters]: result-kind :=
| constructor1: constructor-type
| constructor2: constructor-type
;
```

result-kind は `\Prop`、`\PropKind`、`\Set`、`\SetKind`、`\VType` のいずれかである。
constructor type は `->`、`\forall`、通常の式を組み合わせる。Program inductive の parameter は `\VType`、field は value type である。

```text
\inductive Nat: \Set :=
| zero: Nat
| succ: Nat -> Nat
;

\inductive List[A: \VType]: \VType :=
| nil: List
| cons: A -> List[A] -> List
;
```

constructor は `Type[parameters]::constructor arguments` で参照する。

### structure と record

```text
\record Type[parameters]: result-kind := {
  field1: type1,
  field2: type2,
};

Type[parameters] {
  field1 := value1,
  field2 := value2
}
```

record の field は宣言順に書き、末尾のコンマと空の `{}` を許す。
Set/Prop record の field type は先行 field に依存できる。
Program record は `\VType` で、field は非依存の value type である。

record literal の field 順は任意だが、宣言された全 field を一度ずつ指定する。
projection は `Type[parameters]::field record` または `record #field` である。
Program projection の結果は computation になる。

`\structure` は Set のデータ record と Prop の law record をまとめて宣言する。

```text
\structure EqualPair[A: \Set]: \Set {
  first: A,
  second: A,
} \where {
  same: first = second,
}
```

各 field の型は先行 field に依存できる。
law の型はデータ field と先行する law を参照でき、両者を通して field 名は一意にする。
構築は `EqualPair[A] { first := x, second := x } \with { same := \refl(x) }` と書く。

| 生成される名前 | 意味 |
| --- | --- |
| `EqualPair[A]::[Raw]` | データ record の型 |
| `EqualPair[A]::[Law][r]` | データ `r` に対する law record の型 |
| `EqualPair[A]` | `{ r: EqualPair[A]::[Raw] \where EqualPair[A]::[Law][r] }` |
| `EqualPair[A]::[Set]` | `\Cast[EqualPair[A]::[Raw]] EqualPair[A]` |
| `EqualPair[A]::[raw]` | `EqualPair[A]::[Set]` からデータ record を取り出す関数 |
| `EqualPair[A]::[law]` | `EqualPair[A]::[Set]` から law record を取り出す関数 |

`s: EqualPair[A]::[Set]` に対して `s #first` と `s #same` でデータと law を射影できる。
`::[raw]` は要素を元の record 型として扱い、`::[law]` は部分集合への所属証明を取り出す。

### correspondence

```text
\correspondence identity: A ~> \F(A) {
  \program := \cfun (x: A) => \return x,
  \set := \fun (x: A^) => x,
  \coherence := \refl(identity::[program]^),
}
```

Program とその reflection に対応する Set の項を、等式の証明とともに宣言する。

| 生成される名前 | 型または意味 |
| --- | --- |
| `identity::[Type]` | 注釈した Program 型 `A ~> \F(A)` |
| `identity::[program]` | `identity::[Type]` |
| `identity::[set]` | `identity::[Type]^` |
| `identity::[coherence]` | `identity::[program]^ = identity::[set]` |

本体には `\definition`、`\alias`、`\inductive`、`\record`、`\structure`、`\correspondence`、`\machine`、import、macro の補定義を置ける。
名前は宣言順に解決し、公開 member はその割り当て以降に参照できる。
補定義はその本体内で可視になり、外からは表の member を参照する。

### machine

```text
\machine name {
  \State := State,
  \Output := Output,
  \step := step,
  \terminates := acc,
}
```

全入力について停止する状態機械を宣言する。
`State` と `Output` は Program の value type である。

| 生成される名前 | 型または意味 |
| --- | --- |
| `name::[State]` | 状態の value type |
| `name::[Output]` | 結果の value type |
| `name::[step]` | `\U(State ~> \F(\RunStep[State, Output]))` |
| `name::[terminates]` | `(x: State^) -> \Acc[State^, Output^](name::[step]^, x)` |
| `name::[run]` | `State ~> \F(Output)` |
| `name::[runbox]` | `\Box[State ~> \F(Output)]` |

`name::[run]` は `name::[step]` と `name::[terminates]` を使って `\run` を実行する計算である。
`name::[runbox]` は `\box[_](name::[run])` に展開し、既存の Box の閉性検査に従う。
本体の補定義と可視性は correspondence と同じである。
`::[run]` と `::[runbox]` は本体の末尾で生成する。

### check と評価

Set/Prop:

```text
\check expression: type;
\infer expression;
\eval expression;
\normalize expression;
```

Program:

```text
\vcheck value: value-type;
\vinfer value;
\ccheck computation: computation-type;
\cinfer computation;
\ceval computation;
\cnormalize computation;
```

## 4. 式の共通構文

### binder

```text
(x: A)
(x, y: A, z: B)
(_: A)
(x: A \where predicate)
(x: A \where predicate \as proof)
```

`\where` 付き binder は値の名前を一つだけ取り、条件と任意の証明名を導入する。
`\forall` と `\fun` で使える。

### 優先順位

すべての式は括弧で囲める。強い順の優先順位は次のとおり。

| 構文 | 結合 |
| --- | --- |
| `atom`、括弧 | — |
| `expression::item`、`expression #field` | 左 |
| `keyword atom` | 右 |
| `function argument` | 左 |
| `left = right` | 一度だけ |
| `A -> B`、`A ~> C` | 右 |
| `a \of T`、`a \assign _1` | 左 |

```text
f x y
x y #field z
(x y) #field z
x = y
A -> B -> C
A ~> B ~> C
```

`\let` と `\bind` は `\in` の後を右端まで読む。`\return` も後続の value 式全体を読む。
atom を一つ取る keyword は右結合する。複合式を引数にするときは括弧で囲む。
`x y #field z` は `x (y #field) z` と結合する。`#field{value}` も射影として使える。

### 型注釈

```text
a \of T
f x \of A -> B
(\fun (x: _) => x) \of A -> A
(\return a) \of \F A
```

`a \of T` は `a` を型 `T` で検査し、式全体の型を `T` にする。
注釈は還元で消える。
Set/Prop の項と Program の値・計算に使える。

## 5. Set/Prop

### sort

```text
\Prop
\PropKind
\Set
\Set(2)
\SetKind
\SetKind(2)
```

`\Set` と `\SetKind` の level は省略時 0 である。

### product と lambda

```text
A -> B
\forall (x: A) -> B
\forall (x, y: A) (z: B) -> C
\fun (x: A) => body
\fun (x, y: A) (z: B) => body
```

### set operator

```text
\Pow A
{ x : A \where predicate }
\Cast[A] subset
\In[A] subset element
\into[A](element, subset) \by { membership-proof }
\exists A
\exists {x: A \where P x}
```

`\Pow` は powerset、`\Cast` は refinement type、`\In` は membership predicate、`\into` は membership proof 付きの要素を表す。

### choice

```text
\choice X
\by { existence: existence-proof, uniqueness: uniqueness-proof }

\take (x: A) => body
\by { existence-proof }

\block {
  \takefrom x: A \by existence-proof \then
  \return body
}
```

`\choice` は一意存在する集合の元を返す。
`uniqueness-proof` は `\forall (x, y: X) -> x = y` の証明である。
`\take` と `\takefrom` は存在証明を使って命題を証明する。

### equality と proof term

```text
left = right
\refl element-atom
\exact(element, set)
\bysub(superset, subset, element)
\idelim left = right \with x: A => predicate \by { base: base-proof, equality: equality-proof }
\choiceeq element \of X
  \by { existence: existence-proof, uniqueness: uniqueness-proof }
```

`\choiceeq` は `element = \choice X \by { existence: existence-proof, uniqueness: uniqueness-proof }` を証明する。
集合 X の一意性を、choice の型付けを通じて利用する。
`\of _` の集合は、期待される等式の右辺が choice に展開される場合、その集合から推論する。
choice と choiceeq の証明引数は型検査され、定義的等価性の比較では消去される。

組み込み公理:

```text
\axiom:setext(left, right, left-to-right, right-to-left)
\axiom:funext(left, right, pointwise)
\axiom:classicalIndefiniteChoice(domain, family, inhabited)
```

### inductive elimination

```text
\match scrutinee \in Type \return motive \with {
| constructor1 : branch1
| constructor2 field : branch2
}

\induction (x: Type[parameters]) \return result-type \with {
| constructor1 : branch1
| constructor2 : branch2
}

\prec[Type[parameters], motive] branch1 branch2
```

`\match` と `\induction` の branch は `|` または `}` で終わる。
Set/Prop の `\match` では `\return` に結果型を指定し、branch の見出しで constructor の引数を束縛する。
`\induction` は `x` を result type 内で束縛し、帰納型上の関数を構成する。
`\induction` の branch 本体は constructor の引数と帰納法の仮定を受け取る関数である。
`\prec` は primitive recursor の atom で、後ろに branch を通常の application として渡す。

### logical block

```text
\block {
  \fun (x, y: A) (h: P x) \then
  \let z: B := term \then
  \enough C \by { map } \then
  \return result
}
```

`\fun`、`\let`、`\enough` を 0 個以上並べ、必須の `\return` で終える。
`\fun` は目標の前方に binder を追加する。
`\let` は後続の項と型から展開できる局所定義である。
`\enough A \by { map } \then` は `map: A -> B` を使って残りの目標を `A` にする。

## 6. Program (CBPV)

value type、computation type、value、computation を区別する。

### type

```text
\VType
\F value-type-atom
\U computation-type-atom
A ~> C
\RunStep[A, B]
```

`\F` は value を返す computation type、`\U` は thunk の value type、`~>` は computation function type、`\RunStep` は run の一ステップを表す value type である。

`A -> B` は CBV の糖衣である。computation type の位置では `A ~> \F(B)`、value type の位置では `\U(A ~> \F(B))` と読む。定義の型で裸の `A -> B` は computation type として扱われる。
関数 value の型は `\U(A -> B)` と書く。

### value と computation

```text
\return value
\thunk computation-atom
\force value-atom
\cfun (x: A) => computation
function value
```

computation application の引数は value である。computation の結果を渡すときは `\bind` で受け取る。
`\fun` と `->` も Program の文脈では CBV の糖衣である。`\fun` は computation 位置では `\cfun`、value 位置では thunk された computation になる。複数引数では中間の関数を `\return(\thunk(...))` で返す。

### local binding と Program block

```text
\let x: A := value \in computation
\bind y: B <- computation1 \in computation2

\program {
  \let x: A := value \then
  \bind y: B <- computation \then
  \return result
}
```

`\let` は value、`\bind` は computation の結果を束縛する。型注釈は必須で、名前は `\in` より後だけで有効である。Program block の中間文は `\let` と `\bind` であり、`\then` でつなぐ。終端は `\return value` である。
block の `\let` 名は通常の識別子、`\bind` 名は `_` も使える。

### case

```text
\match scrutinee \in Datatype \with {
| constructor1 : computation1
| constructor2 field1 field2 : computation2
}
```

scrutinee と branch field は value、branch body は computation である。datatype 名は必須。
branch の末尾に `;` は付けない。

## 7. 一般再帰、Run、Box

### RunStep と accessibility

```text
\continue[state-type, result-type](next-state)
\finish[state-type, result-type](output)
\step-match x: \RunStep[state-type, result-type] \return P \with {
  | \continue next-state: M
  | \finish output: N
}
\step-match \RunStep[state-type, result-type] \return C \with {
  | \continue next-state: M
  | \finish output: N
}
```
`\continue` と `\finish` は `\RunStep[state-type, result-type]` 型の値である。
変数 `x` を指定する `\step-match` は Set 側の依存関数 `(x: \RunStep[state-type, result-type]) -> P` を作り、各分岐は `P` に対応する項を返す。
変数を指定しない `\step-match` は Program 側の値 `\U(\RunStep[state-type, result-type] ~> C)` を作り、`C` は固定した computation type、各分岐は computation である。

```
\Acc[state-type, result-type](step, state)
\accintro[state-type, result-type](step, state, predecessors)
\accdescent[state-type, result-type](step, from, to, accessibility, transition)
```

`\Acc` 以下は Set 側の accessibility とその導入・降下である。

### run

```text
\run[state-type, result-type](step, initial) \by { accessibility }
\runCase[state-type, result-type](step, initial, transition) \by { accessibility: accessibility-proof, equality: transition-equality }
```

step は step function、accessibility は停止性証明である。`\runCase` は一回分の transition computation と反映上の等号証明を受け取る。

### Box

```text
\Box[program-computation-type]
\box[program-computation-type](computation)
\squash[program-computation-type](boxed)
\boxapp(boxed-function, boxed-argument)
```

Box の対象は computation type である。value を入れるときは `\F(A)` と `\return value` を使う。

## 8. マクロ

### 定義と可視性

```text
\math-macro name(pattern) := template;
\macro name(pattern) := template;
\use ImportAlias.macroName;
```

同じ module と親 module の可視な macro は直接使える。import した macro は `\use` で導入する。
同名 macro を同時に可視にはできない。

### pattern

pattern の要素はコンマで区切る。

| pattern | 捕捉するもの |
| --- | --- |
| $name | 通常の式一つ |
| name | 記号または引用トークン一つ（名前付き macro） |
| ..name | 残りの列 0 個以上（名前付き macro） |
| \+ | 固定記号トークン |
| "tag" | 固定引用トークン |
| (pattern, ...) | 入れ子の列 |

`..name` は各列の末尾に一つだけ置く。`->`、`~>`、`<-`、`=>`、`:=`、`|`、`:`、`;`、`.`、`,`、`=`、`!`、`::`、`^` は固定 macro token にできない。数式 macro は `$name` capture だけを使う。

### 呼び出しと template

```text
\(x + y \)
name!{x "+" y}
name!{_ f}
name!{{ f x } "keep"}
```

数式 macro は `\( ... \)`、名前付き macro は `name!{ ... }` で呼ぶ。名前と `!` の間に空白を入れない。呼出列の要素はコンマでなく空白または token 境界で並べる。

macro 列内の `( ... )` は常に入れ子の macro 列である。通常の複合式を一つ渡すときは `{ expression }` と書く。その内部では通常の式構文を使う。

template では $name が式 capture、bare name が token capture、..name が列の splice になる。
template の自由な名前は定義側、capture した式は呼出側の scope で解決する。macro の branch
が導入する binder は call-site の名前を捕捉しない。

### token match

名前付き macro の template 内だけで `\tmatch` を使える。

```text
\tmatch token {
| \+ => expression
| "+" => expression
| ($head, ..tail) => expression
| () => expression
| _ => default
}
```

pattern は固定記号、固定引用 token、入れ子の列、_ のいずれかである。branch は上から最初に
一致したものを使う。空の branch 集合も書け、網羅性は要求されない。branch 内の capture はその
branch 本体だけで有効である。

名前付き macro は自分自身を呼べる。それ以外の nested macro は宣言時点で可視だったものだけを
呼べる。macro 展開深さの上限は 128 である。

実行方法と診断は [利用方法](../../../../src/USAGE.md) を参照する。
