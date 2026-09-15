# 表面構文

パーサーは先頭トークンと固定長の先読みで構文を選び、消費したトークンを読み直さない。
構文を選んだ後のエラーは、その構文内のエラーとして報告する。

## 字句と式

キーワードは `\definition` のようにバックスラッシュで始まる。
識別子は英字で始まり、英数字と `_` を使える。Program の名前の参照に `^` を付けると
Set reflection を表す（例: `Bool: \VType` に対する `Bool^: \Set`）。
反映後の constructor は `Bool^::true`、パラメータ付きの型は `Wrap^[Bool^]` と書く。
`Wrap^` の引数は Set の型なので、`Wrap^[\Power(Bool^)]` のようにも使える。
Program の定義や module parameter にも同じ記法を使い、`value: Bool` に対して
`value^: Bool^`、`identity: Bool ~> \F(Bool)` に対して `identity^: Bool^ -> Bool^` となる。
import した名前も `M.Bool^`・`M.value^` と書く。`^` は参照に付く独立したトークンである。
`/* ... */` は入れ子可能なコメント。
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
| `x = y` | 連鎖不可 |
| `A -> B`、`A ~> C` | 同順位、右 |

`T[A, B]` は型・定義の明示的パラメータ指定、`scope.name` は import したスコープへのアクセス。
`T[A]::ctor x y` はコンストラクタへの適用、`T[A]::field value` は field projection。

## Module instance と child module

module path 全体を一度に instance 化するほか、import 済みの generative instance を
起点に child module を instance 化できる。

```text
\import \root.Parent(A := Nat) \as P;
\import P.Child(x := value) \as C;
```

このとき `C` 内から参照される親の型と定義は、同じ引数から再生成された別の親ではなく
`P` のものになる。別途 `P.Child(...)` を実行すれば、child 自体は新しい instance になる。

## 論理側の束縛

```text
\forall (x: A) -> B
\fun (x: A) => body
\fun (x: A) (y: B) => body
\fun (x, y: A) => body
A -> B
```

複数の束縛は左から順にスコープへ入る。匿名ラムダは `\fun (_: A) => body`。
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

Program では通常の call-by-value 関数を `A -> B` とも書ける。値型として読む位置では
`A -> B` を `\U(A ~> \F(B))`、計算型として読む位置では `A ~> \F(B)` に展開する。
定義の型に裸で書いた `A -> B` は計算型として読む。関数値を定義するときは
`\U(A -> B)` と明示する。
`\Box`・`\box`・`\Force` の型指定にある裸の `->` も計算型として読み、関数値を
指定するときは `\U(A -> B)` と明示する。矢印は右結合する。

`~>` の引数は値型、結果は計算型、`\F` の引数は値型、`\U` の引数は計算型として
再帰的に読む。このため `A ~> (B -> C)` は使えるが、`A -> \F(B)` は値型と計算型を
取り違えているためエラーになる。Program の `->` は依存型や refinement 束縛を導入しない。

```text
\definition identity(x: A): \F(A) := \return x;
\definition suspended: \U(A ~> \F(A)) := \thunk identity;
\definition result: \F(A) :=
  \let x: A := a \in
  \bind y: A <- \force suspended x \in
  \return y;
```

`\fun` も同じ CBV 展開を行う。計算位置では外側を `\cfun` にし、値位置ではさらに
`\thunk` で包む。複数引数では、後続の関数を返すために引数間へ
`\return(\thunk(...))` が入る。最後の本体は計算なので、戻り値の `\return` は省略しない。

```text
\definition and: Bool -> Bool -> Bool :=
  \fun (x, y: Bool) =>
    \match x \in Bool \with {
    | false => \return(Bool::false)
    | true => \return(y)
    };
```

この定義の型は `Bool ~> \F(\U(Bool ~> \F(Bool)))`、本体は
`\cfun (x: Bool) => \return(\thunk(\cfun (y: Bool) => ...))` に展開される。

`\cfun` は複数の括弧付き束縛や同じ型の複数名を受け付ける。Program の束縛には
refinement を指定しない。関数の適用は `computation value` と書き、左結合する。
例えば `f x y` は `(f x) y`、`\force f x` は `(\force f) x`。
引数は値であり、計算結果を引数にする場合は先に `\bind` で受け取る。
通常の計算関数は直接適用する。`\U(A ~> C)` の関数値を適用する場合は
`\force f` と明示する。カリー化された計算の途中で `\F(\U(A ~> C))` が得られる場合も、
結果を明示的な `\bind` で受け取り、その値を `\force` してから次の引数を渡す。
引数位置の計算も同様に明示的な `\bind` が必要であり、`f (g x)` の `g x` が計算なら
そのまま引数にはできない。`return`・`thunk`・`force`・`bind` の自動挿入は行わない。

`\definition f(x: A, y: B): C := body;` は型 `A ~> B ~> C` と本体
`\cfun (x: A) (y: B) => body` に展開する。`f(x, y: A)` や `f(x: A)(y: B)` も使える。
この省略記法は型関連の計算定義にも使える。

`\return` は後続の値式全体を引数とする。`\force`・`\thunk` は一つの atom と
その関連アクセスを引数とし、複合式は括弧で囲む。
例えば `\return Pair::pair x y`、`\thunk (\cfun (x: A) => \return x)`。

`\let x: A := value \in body` は値を、`\bind x: A <- computation \in body` は
計算結果を束縛する。型注釈は必須で、推論には `_` を使う。
名前は本体でのみ有効。型注釈と右辺は外側のスコープで解釈する。本体は計算式。
束縛は式の先頭で解析し、本体を右端まで読む。適用の引数として置く場合は括弧で囲む。
例えば `f (\thunk (\let x: A := a \in \return x))`。
この式形式の束縛の区切りには `\in` を使う。`;` は宣言・命令やブロック内の文の末尾に置く。

連続する束縛は Program ブロックでも書ける。

```text
\block {
  \let x: A := value;
  \bind y: B <- computation;
  \return result;
}
```

ここで `\let` と `\bind` の束縛は後続の文で有効になり、末尾の
`\return` は値を Program computation として返す。論理側の `\block` と同じ表面構文だが、
期待されるカテゴリに応じて Program の `ValueLet`／`Sequence`／`Return` に分類される。

```text
\match value \in Datatype \with {
  | empty => \return fallback
  | pair left right =>
      \bind result: B <- f left \in
      \return result
}
```

対象の型名は必須。分岐にはコンストラクタ名とその直下の変数名を並べる。
入れ子のパターンやガードは使わない。引数は値として束縛される。
分岐本体は次の `|` または閉じ括弧 `}` までで、末尾に `;` は付けない。
`\elim`・`\tmatch` の分岐も同じ区切りを使う。分岐内の `\block` の文末には `;` が必要。
分岐は型のコンストラクタ宣言順に一つずつ書く。現在の型分類では対象の値の型が
この時点で判明している必要があるため、直前の束縛で型が `_` のままなら型名を明示する。
再帰・反映の `\Prun`・`\Pcontinue`・`\box` などは従来の専用構文を使う。

`\Prun(A, B, step, initial) \by p` の停止性証明 `p` は必須である。
`p` は Program の引数を Set 側へ反映した `\Acc(A, B, step, initial)` の証明として検査する。
`\PrunCase(A, B, step, initial, transition) \by (p, edge)` では、さらに
`edge` として反映後の `step initial = transition` の証明を渡す。
証明中では Program の名前付き型・値・計算を Set 側へ反映して参照できる。
証明は Program 項に保持され、代入・モジュール具体化・簡約に伴って更新されるが、計算上の比較には影響しない。

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

`\definition` は名前・型・`:=`・本体・`;` の順で、宣言した型と本体から
Set/Prop、Program value、Program computation のいずれかを判定する。
名前の後には括弧付き引数を付けられる。
`\module Name(parameters) { ... }` は入れ子のモジュール、`\module Name;` は外部ファイル。
`\import M(argument := value) \as Alias;` でモジュールを実体化する。

実行方法と診断は [利用方法](../../../../src/USAGE.md)、
型関連のアクセスは [型関連 item](types_and_items.md) を参照。
