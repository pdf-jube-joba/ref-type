# 表面構文

現在の `.ref` ファイルで使われている表面構文を、目的別にまとめる。
例中の `<...>` は実際の名前や式に置き換えるメタ記号である。

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

その他の記号列は一つのマクロトークンになる。
別々の記号トークンを隣接させる場合は空白で区切る。

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
定義の宣言型は本体の lambda へ期待型として渡されるため、射影や存在消去に使う引数の注釈も `_` にできる。
複数変数の束縛、ブロック、型注釈付き局所定義でもこの期待型を使い、部分集合型を保持する。

```text
\definition andElim(P, Q, R: \Prop): (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value #left) (value #right);
```

共有する推論変数の解は、各出現に共通する外側の binder に依存できる。
束縛名の `_` は匿名名である。

Set/Prop の式には `\assign` で番号付き推論変数との等式を登録できる。
式を elaboration した時点で制約を解き、同じ宣言の型注釈と本体で共有する。
式の値は左辺のままで、既に解がある場合は整合性を検査する。
`\assign` の結合順位は矢印より弱い。

```text
\definition Relation[A: \Set]: \PropKind := A -> A -> \Prop;
\definition diagonal(A: \Set)(R: Relation[A] \assign _1): _1 := R;
```

`?` がある module の elaboration は失敗し、その位置の期待型、ローカル変数、関連する制約を報告する。
制約から項が求まった場合も hole を報告し、求まった項を表示する。
同じ宣言に未解決の推論変数がある場合は、それらも一緒に表示する。

診断では、情報不足、他の metavariable の解待ち、solver が扱えない制約、制約の矛盾を区別する。
制約にはソース上の metavariable の番号、発生位置、解決前後の式を表示する。

## 2. module

ルートファイルには module を一つ以上置く。module は入れ子にできる。
通常の項名は宣言位置の文脈で解決し、macro の定義と使用宣言は本体全体と子 module に有効である。

```text
\module Name(parameters) {
  <module-item>*
}

\module Name(parameters);
```

`;` で終わる宣言は外部 module で、対応する `Name.ref` に module item を置く。
子 module のファイルパスは module の入れ子に対応する。

### import

```text
\import .Child[A := T] \as C;
\import \parent.Sibling[] \as S;
\import \parent.\parent.Outer[] \as O;
\import my_package.Top[A := T] \as T;
\import my_package.Top[A := T].Nested[] \as N;
\import ExistingAlias.Child[x := value] \as Child;
```

parameter の個数・名前・順序を宣言と一致させる。
先頭の `.` は現在の module、パッケージ名はそのルート、`\parent.` は一つ上の module から探索する。
module argument では metavariable の推論を行わない。

### 式中の具体化

```text
\definition carrier(A: \Set): \Set := Family[A := A].Carrier;
\definition disk(n: Nat^): \Set := Euclidean.Dimension[n := n].Disk;
\structure Cell: \Set {
  dimension: Nat^,
  point: Euclidean.Dimension[n := dimension].Disk,
}
```

参照の位置で module 引数を検査し、具体化した module の item を取り出す。
関数の引数や record の先行 field を参照できる。
帰納型の具体化と Program の局所値を渡す例は、[module 具体化のテスト](../../../../src/elaboration/tests/module_expressions.rs) を参照。

## 3. 宣言

### definition

```text
\definition name: type := expression;
\definition name(x, y: A)(z: B): type := expression;
\definition Type(parameters)::item(arguments): type := expression;
```

括弧付き binder は複数 group 書ける。
`:` の左の binder を宣言文脈に追加して、結果の型と本体を検査する。
型と本体から Set/Prop、Program value、Program computation のいずれかに分類される。
`Type::item` は型関連 item で、owner の parameter を先頭に持つ宣言になる。

### 文脈付きの definition

```text
\definition Relation[Carrier: \Set]: \PropKind := Carrier -> Carrier -> \Prop;
\definition At[A: \Set, x: A, P: A -> \Prop]: \Prop := P x;
```

適用時に各引数を検査し、宣言の引数へ代入して結果を具体化する。
product 型を形成できる定義は通常の関数として使える。
部分適用では、渡した引数を代入した後、残りの引数について既存の product rule を満たす場合に関数へ変換できる。

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

### structure

関連型・操作・法則をまとめる宣言の束と、sort を指定した record を扱う。
宣言・literal・既定値・量化は [structure](structure.md)、型関連定義と射影は [型関連 item](types_and_items.md) を参照。

### 実装と仕様、状態遷移

`std.Program` は実装と仕様の対応を `Correspondence`、停止性を持つ状態遷移を `Machine` として提供する。

```text
\import std.Program[] \as P;
\definition identity: P.Correspondence := P.Correspondence {
  T := \U(A ~> \F(A)),
  program := \thunk(\cfun(x: A) => \return x),
  specification := \fun(x: A^) => x,
  coherence := \refl(\fun(x: A^) => x),
};
```

`identity.program` は thunk の値、`identity.specification` は反映先の仕様、`identity.coherence` は両者の等式である。
`Machine` の `State`、`Output`、`step`、`terminates` を実装すると、`run` の既定値が停止性証明を使って実行する。
具体化された Machine の実行は `runBox` マクロで Box にする。

```text
\use P::runBox;
runBox!{machine}
```

展開した計算は、呼出側で Box の閉性検査を受ける。

### check と評価

Set/Prop と Program に共通の文を使う。
`\check` は指定された型、`\infer`・`\eval`・`\normalize` は式と参照先に応じて処理する。

```text
\check expression: type;
\infer expression;
\eval expression;
\normalize expression;

\check value: value-type;
\infer value;
\check computation: computation-type;
\infer computation;
\eval computation;
\normalize computation;
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
\idelim left = right \with x: A => family \by { base: base-term, equality: equality-proof }
\transporteq index \with x: A => family \by { base: base-term }
\choiceeq element \of X
  \by { existence: existence-proof, uniqueness: uniqueness-proof }
```

`\idelim` の族 `family` は `\Prop` または `\Set(i)` を値に取る。
`base-term` は始点での族の項であり、`equality-proof` によって終点での族へ移送する。
集合値の移送の head は neutral であり、自己移送の恒等性は `\transporteq` で命題上の等式として証明する。
`\transporteq` は集合値の族に対して、`index` から同じ `index` への移送と `base-term` の等式を証明する。
添字の型 `A` は `_` で推論でき、移送の等式証明は型検査後の定義的等価性の比較では消去される。

```text
\module Transport(A: \Set, F: A -> \Set, a, b: A) {
  \definition cast(value: F a)(same: a = b): F b :=
    \idelim a = b \with x: _ => F x \by { base: value, equality: same };
  \definition identity: \forall (value: F a)(same: a = a) ->
    (\idelim a = a \with x: _ => F x \by { base: value, equality: same }) = value :=
    \fun (value: F a)(same: a = a) =>
      \transporteq a \with x: _ => F x \by { base: value };
}
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
```

`\match` と `\induction` の branch は `|` または `}` で終わる。
Set/Prop の `\match` では `\return` に結果型を指定し、branch の見出しで constructor の引数を束縛する。
`\induction` は `x` を result type 内で束縛し、帰納型上の関数を構成する。
`\induction` の branch 本体は constructor の引数と帰納法の仮定を受け取る関数である。
添字付き帰納型では、添字に続けて要素を束縛する。

```text
\induction (n: Nat) (xs: Vec[A] n) \return P n xs \with {
| nil: base
| cons: step
}
```

結果型は binder の文脈で型として検査する。
たとえば `\return \Prop` や `\return Real -> Real -> \Prop` は `\PropKind` に分類され、Set の帰納型から命題や述語を再帰的に構成できる。
枝はこの結果型を constructor に代入した型を持ち、再帰的な引数の直後に、その引数での帰納法の仮定を受け取る。

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

### RunStep

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

### 停止性

Set 側の `State`、`Output` と `step: State -> \RunStep[State, Output]` に対して、停止性を通常の命題として定義する。

```ref
\import std.Logic[].Termination[
  State := State, Output := Output, step := step
] \as T;
```

`T.Holds initial` は次の型に展開する。

```ref
\forall (P: State -> \Prop) ->
  (\forall (x: State) -> T.ready P (step x) -> P x) -> P initial
```

`T.ready P` は `continue next` に対して `P next`、`finish output` に対して `\forall (Q: \Prop) -> Q -> Q` を返す。
`T.intro state certificate` は `certificate: T.ready T.Holds (step state)` から `T.Holds state` を証明する。
`T.descent from to termination edge` は `termination: T.Holds from` と `edge: step from = \continue[State, Output](to)` から `T.Holds to` を証明する。

### run

```text
\run[state-type, result-type](step, initial) \by { accessibility }
\runCase[state-type, result-type](step, initial, transition) \by { accessibility: accessibility-proof, equality: transition-equality }
```

step は step function、accessibility は上記の停止性証明である。
Program 側では state type、result type、step、initial を reflection した停止性条件を使う。
`\runCase` は一回分の transition とその等号証明を受け取り、Program 側では transition computation と反映上の等号証明を使う。

### Box

```text
\Box[program-computation-type]
\box[program-computation-type](computation)
\squash[program-computation-type](boxed)
\boxapp(boxed-function, boxed-argument)
```

Box の対象は computation type である。value を入れるときは `\F(A)` と `\return value` を使う。

## 8. マクロ

数式マクロは `\( ... \)`、名前付きマクロは `name!{ ... }` で呼ぶ。
定義・pattern・展開の規則は [マクロ](macro.md) を参照。

実行方法と診断は [利用方法](../../../../src/USAGE.md) を参照する。
