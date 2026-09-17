# 表面構文
パーサーがなるべく読み直しを起こさないように構文を作りたい。

## 字句と式

- `/* ... */` は入れ子可能なコメント。
- キーワードは `\definition` のようにバックスラッシュで始まる。
- 識別子は英字で始まり、英数字と `_` を使える。
- Program 側の名前の参照に `^` を付けるとSet reflection を表す（例: `Bool: \VType` に対する `Bool^: \Set`）。
  - 反映後の constructor は `Bool^::true`、パラメータ付きの型は `Wrap^[Bool^]` と書く。
  - `Wrap^` の引数は Set の型なので、`Wrap^[\Power(Bool^)]` のようにも使える。
  - Program の定義や module parameter にも同じ記法を使う。
    - `value: Bool` に対して `value^: Bool^`
    - `identity: Bool ~> \F(Bool)` に対して `identity^: Bool^ -> Bool^`
  - import した名前も `M.Bool^`・`M.value^` と書く。`^` は参照に付く独立したトークンである。
- 記号列はまとめて字句解析されるので、隣り合う別々の記号トークンは空白で区切る。
- `->`・`~>`・`<-`・`=>`・`:=` などの予約記号はマクロの演算子に使えない。
- `_` は制約から補完する implicit hole。解が確定しなければ ambiguity error。
- `?` は出現ごとに fresh な goal、`?2` などの番号付き goal は一つの宣言内で共有する。
- 束縛名の `_` は匿名束縛であり、式位置の implicit hole とは異なる。
- sort は `\Prop`・`\PropKind`・`\Set`・`\SetKind`。Set 系は `\Set(2)` のように level を指定でき、省略時は 0。
- `[]` はパラメータ指定用。`T[A, B]` は型・定義へのパラメータ指定。
- `.` は `scope.name` は import したスコープへのアクセス。
- `::` は `T[A]::ctor x y` とかでコンストラクタへの適用とか field projection

式には `(expression)` で括弧を付けられる。優先順位は強い順に以下となる。

| 構文 | 結合 |
| --- | --- |
| `value::field` | 左 |
| `f x y` | 左 |
| `x = y` | 連鎖不可 |
| `A -> B`、`A ~> C` | 同順位、右 |

## Module instance と child module

module path 全体を一度に instance 化するほか、import 済みの generative instance を
起点に child module を instance 化できる。

```text
\import \root.Parent[A := Nat] \as P;
\import P.Child[x := value] \as C;
```

このとき `C` 内から参照される親の型と定義は、同じ引数から再生成された別の親ではなく
`P` のものになる。別途 `P.Child[...]` を実行すれば、child 自体は新しい instance になる。
module path の各要素には `[]` が必須で、宣言された parameter は名前と宣言順を
一致させてすべて指定する。parameter のない module も `Module[]` と書く。
module argument では `_`・`?`・番号付き goal を使った推論も行わない。

## 論理側の束縛

```text
\forall (x: A) -> B
\fun (x: A) => body
\fun (x: A) (y: B) => body
\fun (x, y: A) => body
A -> B
```

refinement を持つ束縛は次のように書く。`\where` は条件、`\as` はその証明名。

```text
\forall (x: A \where P x) -> B
\fun (x: A \where P x \as h) => body
\exists A
\exists {x: A \where P x}
\take (x: A) => body \by { existence: existence, uniqueness: uniqueness }
\take (x: A) => body \by { existence: existence }
```

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

### ブロック記法

`\block { ... }` の中で文を並べて項を構成できる。
`\fix`・`\let`・`\enough` の文に続き `\return expression;` で終える。
最終的な型が `B` のとき、`\enough A \by t;` は `t: A -> B` を適用し、
後続ブロックが作る項の型を `A` にする。

> [!note]
> 論理側の `\let x: A := value;` は局所定義で、
> 後続の項や型を検査するときに `x` の定義内容を展開できる。
> 例えば次の証明は型検査を通る。
> ```text
> \block {
>   \let x: A := a;
>   \let h: x = a := \refl(a);
>   \return h;
> }
> ```

名前は後続の文だけで有効。
型注釈と右辺は定義前のスコープで解釈し、内側の同名の束縛は外側の名前を隠す。

## Program
call by push value でやっているので値と計算が分かれている。

- `\VType`/`\CType` は値/計算型の sort
- `\F(A)` は値を返す計算の型、`\U(C)` は計算を thunk にした値の型。
  - `\F` の引数は値型、`\U` の引数は計算型として再帰的に読む。
- CBPVの普通の計算関数型は `A ~> C` と書く。
  - これを解釈するときは `A` は値、 `C` は計算型として読む。
- 通常の call-by-value 関数を `A -> B` とも書ける。
  - 値型として読む位置位置なら `\U(A ~> \F(B))`
  - 計算型として読む位置なら `A ~> \F(B)`
  - 定義の型に裸で書いた `A -> B` は計算型として読む。
  - 関数値を定義するときは `\U(A -> B)` と明示する。
  - `\Box`・`\box`・`\Force` の型指定は計算型として読む。
- `->` を使っているが依存型や refinement は書けない

```text
\definition identity(x: A): \F(A) := \return x;
\definition suspended: \U(A ~> \F(A)) := \thunk identity;
\definition result: \F(A) :=
  \let x: A := a \in /* これは値の bind 用*/
  \bind y: A <- \force suspended x \in /* これは計算の sequence */
  \return y;
```

`\fun` も同じ CBV 展開を行う。
計算位置では外側を `\cfun` にし、値位置ではさらに `\thunk` で包む。
複数引数では、後続の関数を返すために引数間へ `\return(\thunk(...))` が入る。
最後の本体は計算なので、戻り値の `\return` は省略しない。

```text
\definition and: Bool -> Bool -> Bool :=
  \fun (x, y: Bool) =>
    \match x \in Bool \with {
    | false => \return Bool::false
    | true => \return y
    };
```
- 型は `Bool ~> \F(\U(Bool ~> \F(Bool)))`
- 本体は `\cfun (x: Bool) => \return(\thunk(\cfun (y: Bool) => ...))`

`\definition f(x: A, y: B): C := body;` は型 `A ~> B ~> C` と本体 `\cfun (x: A) (y: B) => body` に展開する。

`\force`/`\thunk` は atom をとるが、 `\return` は後続の値式全体を引数とする。
連続する束縛は Program ブロックでも書ける。

```text
\program {
  \let x: A := value;
  \bind y: B <- computation;
  \return result;
}
```

### Program 側 match
`\match` で同じように見えるが、原始帰納法用ではないので再帰ではない。
完全なパターンマッチ。

```text
\match value \in Datatype \with {
  | empty => \return fallback
  | pair left right =>
      \bind result: B <- f left \in
      \return result
}
```

引数は値として束縛される。
現在の型分類では対象の値の型がこの時点で判明している必要があるため、
直前の束縛で型が `_` のままなら型名を明示する。

再帰・反映の `\run`・`\continue`・`\box` などは専用構文を使う。

- `\run(A, B, step, initial) \by p` の停止性証明 `p` は必須である。
  - `p` は Program の引数を Set 側へ反映した `\Acc(A, B, step, initial)` の証明として検査する。
- `\runCase(A, B, step, initial, transition) \by (p, edge)` では、 `edge` として反映後の `step initial = transition` の証明を渡す。

## レコード

```text
\structure Point(A: \Set): \Set := { x: A, y: A };
\definition point(A: \Set, a: A): Point[A] :=
  \record Point[A] { x := a, y := a };

\structure Point(A: \VType): \VType := { x: A, y: A };
```

生成には `\record` が必須。空のレコード本体も `{}` と書ける。

## マクロ

`\( ... \)` は数式マクロ、`name!{ ... }` は名前付きマクロ。
マクロ内の `(...)` は常にマクロ列とする。通常の複合式は `{ ... }` で渡す。
その内部では括弧を通常の式として使える。識別子などの atom は直接渡せる。

```text
\( (x + y) + { f (g z) } \)
tagged!{{ f x } "keep"}
```

パターン定義、可視性、衛生性は [マクロ](macro.md) を参照。

## 宣言とモジュール

`\definition` は名前・型・`:=`・本体・`;` の順で、宣言した型と本体から
Set/Prop、Program value、Program computation のいずれかを判定する。
名前の後には括弧付き引数を付けられる。
`\module Name(parameters) { ... }` は入れ子のモジュール、`\module Name;` は外部ファイル。
`\import M[argument := value] \as Alias;` でモジュールを実体化する。

実行方法と診断は [利用方法](../../../../src/USAGE.md)、
型関連のアクセスは [型関連 item](types_and_items.md) を参照。
