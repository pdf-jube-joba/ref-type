# マクロ

同じ module と親 module の可視なマクロは直接使い、別の module のマクロは `\use` で導入する。
定義と使用宣言は module の本体全体と子 module に有効であり、子の同名 binding は親を隠す。
同じ module 内の導入名の重複は、定義と使用宣言のどちらでもエラーとなる。

```text
\math-macro add($left, \+, $right) := operation $left $right;
\macro tagged($term, "keep") := $term;
\use ImportAlias::macroName;
\use ImportAlias::Child[A := A]::macroName \as child_macro;
\use \root.Templates[A := A, refl := leftRefl]::reflexive \as refl_left;
\use \root.Templates[A := A, refl := rightRefl]::reflexive \as refl_right;

\(x + y \)
tagged!{value "keep"}
```

`\use` では import alias からの選択と module の直接具体化を使える。
同じ定義元を異なる引数で具体化した場合も、異なる導入名で併用できる。

```text
\module Example(A: \Set, a, b: A) {
  \definition before: a = a := \refl(value!{});
  \macro value() := a;
  \module Child {
    \definition law: b = b := \refl(value!{});
    \macro value() := b;
  }
}
```

## Pattern と呼び出し

定義の pattern はコンマで区切り、呼び出しの列は空白または token 境界で並べる。
マクロ名と `!` は隣接させる。

| pattern | 捕捉・照合するもの |
| --- | --- |
| `$name` | 通常の式一つ |
| `name` | 記号または引用トークン一つ（名前付きマクロ） |
| `..name` | 残りの列（名前付きマクロ、各列の末尾に一つ） |
| `\+` | 固定記号トークン |
| `"tag"` | 固定引用トークン |
| `(pattern, ...)` | 入れ子の列 |

予約記号 `->`、`~>`、`<-`、`=>`、`:=`、`|`、`:`、`;`、`.`、`,`、`=`、`!`、`::`、`^` は固定マクロトークンにできない。
数式マクロの capture は `$name` に限る。
通常の複合式を一つ渡す場合は `{ f x }`、入れ子のマクロ列は `( ... )` で書く。

template の自由な名前は定義側、capture した式は呼出側の scope で解決する。
マクロが導入する binder は呼出側の名前を捕捉しない。
数式マクロは各括弧階層の列全体を照合し、候補が複数なら固定トークンが最も左にあるもの、次に呼び出しスコープからの距離、最後に各 module の導入位置の順で選ぶ。

## Token match と再帰

名前付きマクロの template では `\tmatch` を使える。

```text
\macro last(..r) := \tmatch r {
  | () => defaultValue
  | ($t) => $t
  | ($t, ..rest) => last!{..rest}
};
```

`defaultValue` は定義済みの式とする。
枝は上から最初に一致したものを選び、選んだ枝だけを展開する。
固定記号・引用トークン・列を照合でき、`_` は任意の入力に一致する。
網羅性は要求せず、実際の呼び出しで一致しなければエラーにする。
枝の capture はその枝でだけ有効で、自由な名前は全枝で宣言時に検証する。

> [!warning]
> 括弧列を自動的に平坦化することはない。

template 内の macro は定義元の完成したスコープに結び付き、後に宣言された macro への参照と相互再帰を利用できる。
別名で導入しても内部参照と自己参照には定義元の具体化を使う。
通常の項名は定義位置、使用宣言の module 引数はその宣言位置の項環境で解決する。
module のヘッダーと parameter の型は親の macro スコープを使う。
具体化の依存が循環した場合は、依存経路と宣言位置を報告する。
展開深さの上限は 128 である。
