# 表面構文

パーサーは先頭トークンと固定長の先読みで構文を選び、消費したトークンを読み直さない。
構文を選んだ後のエラーは、その構文内のエラーとして報告する。

## 字句と式

キーワードは `\definition` のようにバックスラッシュで始まる。
識別子は英字で始まり、英数字と `_` を使える。`/* ... */` は入れ子可能なコメント。
記号列はまとめて字句解析されるので、隣り合う別々の記号トークンは空白で区切る。
`->`・`~>`・`<-`・`=>`・`:=` などの予約記号はマクロの演算子に使えない。

- `_` は制約から補完する implicit hole。解が確定しなければ ambiguity error。
- `?` は出現ごとに fresh な goal、`?2` などの番号付き goal は一つの宣言内で共有する。
- 束縛名の `_` は匿名束縛であり、式位置の implicit hole とは異なる。
- sort は `\Prop`・`\PropKind`・`\Set`・`\SetKind`。Set 系は `\Set(2)` のように level を指定でき、省略時は 0。

式には `(expression)` で括弧を付けられる。優先順位は強い順に以下となる。

| 構文 | 結合 |
| --- | --- |
| `value::field` | 左 |
| `f x y` | 左 |
| `x \| f`（`f x` の意味） | 左 |
| `x = y` | 連鎖不可 |
| `A -> B`、`A ~> C` | 同順位、右 |

`T[A, B]` は型・定義の明示的パラメータ指定、`scope.name` は import したスコープへのアクセス。
`T[A]::ctor x y` はコンストラクタへの適用、`T[A]::field value` は field projection。

## 論理側の束縛

```text
\forall (x: A) -> B
\fun (x: A) => body
\fun (x: A) (y: B) => body
\fun (x, y: A) => body
A -> B
```

複数の束縛は左から順にスコープへ入る。匿名ラムダは `\fun (_: A) => body`。
接頭辞のない `(x: A) -> B`・`(x: A) => body`・`A => body` は使わない。
帰納型のコンストラクタ型・添字にも、依存する積型には `\forall` を使う。

refinement を持つ束縛は次のように書く。`\where` は条件、`\as` はその証明名。

```text
\forall (x: A \where P x) -> B
\fun (x: A \where P x \as h) => body
\exists A
\exists {x: A \where P x}
\take (x: A) => body \by (existence, uniqueness)
```

refinement 束縛では値の名前は一つ。証明名の利用可否や存在・選択の意味上の制約は
従来の型規則に従う。Prop の選択では `\by (existence)` とする。
条件付き束縛の旧 `((x: A) | P)` と `((x: A) | h: P)` は使わない。

集合・証明の専用演算は従来の関数形式を使う。

```text
\Power(A)
\Subset(x, A, P x)
\Pred(A, X, a)
\Ty(A, X)
\subsetinto(A, X, a, proof)
\exact(a, A)
\refl(a)
\axiom:funext(f, g, pointwise)
```

`\block { ... }` は論理側のブロック。`\fix`・`\let`・`\take` の文に続き、
`\return expression;` で終える。Program の `\let ... \in` とは別の構文・意味を持つ。

## Program（CBPV）

値の型と計算の型を区別する。`\VType` は値型の sort、`\F(A)` は値を返す計算の型、
`\U(C)` は計算を thunk にした値の型。計算関数型は `A ~> C` と書く。

```text
\cdefinition identity(x: A): \F(A) := \return x;
\vdefinition suspended: \U(A ~> \F(A)) := \thunk identity;
\cdefinition result: \F(A) :=
  \let x: A := a \in
  \bind y: A <- \force suspended x \in
  \return y;
```

`\cfun` は複数の括弧付き束縛や同じ型の複数名を受け付ける。Program の束縛には
refinement を指定しない。関数の適用は `computation value` と書き、左結合する。
例えば `f x y` は `(f x) y`、`\force f x` は `(\force f) x`。
引数は値であり、計算結果を引数にする場合は先に `\bind` で受け取る。
`return`・`thunk`・`force` を自動では挿入しない。

`\cdefinition f(x: A, y: B): C := body;` は型 `A ~> B ~> C` と本体
`\cfun (x: A) (y: B) => body` に展開する。`f(x, y: A)` や `f(x: A)(y: B)` も使える。
この省略記法は型関連の計算定義にも使える。`\vdefinition` は関数引数を受け付けない。

`\return` は後続の値式全体を引数とする。`\force`・`\thunk` は一つの atom と
その関連アクセスを引数とし、複合式は括弧で囲む。
例えば `\return Pair::pair x y`、`\thunk (\cfun (x: A) => \return x)`。

`\let x: A := value \in body` は値を、`\bind x: A <- computation \in body` は
計算結果を束縛する。型注釈は必須で、推論には `_` を使う。
名前は本体でのみ有効。型注釈と右辺は外側のスコープで解釈する。本体は計算式。
束縛は式の先頭で解析し、本体を右端まで読む。適用の引数として置く場合は括弧で囲む。
例えば `f (\thunk (\let x: A := a \in \return x))`。
束縛の区切りに `;` は使わず、宣言や分岐の末尾にだけ置く。

```text
\match value \in Datatype \with {
  | empty => \return fallback;
  | pair left right =>
      \bind result: B <- f left \in
      \return result;
}
```

対象の型名は必須。分岐にはコンストラクタ名とその直下の変数名を並べる。
入れ子のパターンやガードは使わない。引数は値として束縛され、各分岐の末尾には `;` が必要。
分岐内でも `x | f` のパイプ適用を使える。
分岐は型のコンストラクタ宣言順に一つずつ書く。現在の型分類では対象の値の型が
この時点で判明している必要があるため、直前の束縛で型が `_` のままなら型名を明示する。
旧 `\capp`・`\do`・`\case` および `\CFun`・`\clam`・`\sequence`・`\vlet`・`\vcase` は使わない。
再帰・反映の `\Prun`・`\Pcontinue`・`\box` などは従来の専用構文を使う。

## レコード

```text
\structure Point(A: \Set): \Set := { x: A, y: A };
\definition point(A: \Set, a: A): Point[A] :=
  \record Point[A] { x := a, y := a };
```

生成には `\record` が必須。空のレコード本体も `{}` と書ける。
パーサーと未分類 AST はレコードを論理側に限定しない。型名・パラメータ・フィールド式を
保持し、後段で分類する。Program の structure も同じ表面構文を使う。

## マクロ

`$( ... $)` は数式マクロ、`name!{ ... }` は名前付きマクロ。
マクロ内の `(...)` は常にマクロ列とする。通常の複合式は `{ ... }` で渡す。
その内部では括弧を通常の式として使える。識別子などの atom は直接渡せる。

```text
$( (x + y) + { f (g z) } $)
tagged!{{ f x } "keep"}
```

パターン定義、可視性、衛生性は [マクロ](macro.md) を参照。

## 宣言とモジュール

`\definition`・`\vdefinition`・`\cdefinition` は名前・型・`:=`・本体・`;` の順。
論理側の定義と `\cdefinition` には名前の後に括弧付き引数を付けられる。
`\module Name(parameters) { ... }` は入れ子のモジュール、`\module Name;` は外部ファイル。
`\import M(argument := value) \as Alias;` でモジュールを実体化する。

実行方法と診断は [利用方法](../../../../src/USAGE.md)、
型関連のアクセスは [型関連 item](types_and_items.md) を参照。
