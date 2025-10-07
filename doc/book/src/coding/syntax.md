# code での文法の検討
- checker 用の命令は `#` で始まる
  - `#include` ... 他の読むべきファイルを連結する（ファイルの頭に）
  - `#eval` ... normalize する
- ファイルに対してではなくて、 それの中身を（適当な順で並べた） `module` の集まりを処理することを考える。
  - 本当は `module` の順は不問としたいけど、実装の都合とかがあるので、しばらくは順序を指定することにする。
- なるべく機械と目でのパースを楽にするため、目的ごとに記号を分ける。
- 基本的には、パースの際に空白で区切ったものが token になるようにする。
- ユーザーが処理するように自由に使える token と、言語側で予約している token をわける。
  - `'name` と `'variable` は identifier にする。
    - 気持ち的には、 `'name` は展開されないやつで、 `'variable` は展開されるやつ。
  - `'number` はそのまま数字のこと
  - `'macro` は `'name` の後に空白無しで `!` とする。
    - 例： `reasoning!`, `either!`
  - `'macro-acceptable` は token 側とかぶらないようなやつのこと。 
    - 例： `"mod"`, `+++`, `!hello` は acceptable
    - ダメな例： `:` は記法がかぶるのでダメ。
- 記号の解釈を選ぶ必要があるような部分を明示的に書くための文法として `$(` から `$)` で囲むことができるようにする。
  - context を選ぶ場合には、 `$ ... )` の間に何か書く。
  - これは別のやり方の方が読みやすいかも。
- refinement のようなことをする部分では、常に `|` を書いていいほうがうれしい。
  - 普通の subset を扱うときは `(x: \Ty({x: A | P}) ) => ...` のように書くのはめんどくさいので、 `(x: A | P) => (some x occurence)` と書きたい
  - set の nonempty も、 `\exists { x: A | P } => ...` は嫌かもしれないから、 `\exists (x: A | P) => (some x occurence)` とか
  - take も `\Take x: A. ...` 以外に `\Take (x: A | P). (some x occurence)` とか。
- module と定義の展開とか等しさの定義を考える。

## 今はちょっと置いておく部分
- 数学的構造の話には Record 型"のようなもの"を使う。
  - 項は nominal にするために `RecordName { fiele := expression}` とする。
  - 一般の Record 型が混ざると話がややこしい（帰納型で十分に記述できる）ので、数学的構造を扱うことを念頭に考える。
  - 構造の性質については、構造に含めずに、 subset を記述しやすくするものと考えて、形容詞みたいに扱えるようにしたい。
- `import a.b` や `import a.*` の仕組みや std は自動的に import されるみたいな仕組みを考える。
- 使うかもしれない記法のメモ
  - `a@b`

# 構文（案）
## 概要
- 式、文、ブロックによる構造化
  - 'exp := ... | 'block
  - 'block := "{" ('stmt)* 'exp "}"
  - 'stmt := "fix" (x: A) ";" | "have" x: A := t ; | ...
- where と proof で証明の補助を明示的に書く
  - 例：
    ```
    definition x: A := t where {
      - l1: P1 := p1;
      - l2: P2 := p2;
    } proof {
      - goal: P3 := p3;
      - goal: P4 := p4;
    }
    ```
- parametrized module の入れ子とアクセスを簡単に
  - `module Name((param : paramtype)* ) { ... }` で module にパラメータを
  - `ModName(param := arg)` で module に引数を与える
  - `a.b.c.d` 記法
  - `import ModName(param := arg) as AnotherName` で簡単なアクセスができるように
- 型チェックの中で proof の構成が要求されることがある...expression の一部として組み込んだりすることにする。
  - 型チェックある所に proof あるので全部に `'proof` 句がくるように syntax を調整しないと。

## 全体
ここは core calculus + α ぐらい。

## exp
- `'exp` = either
  - 普通じゃないやつ
    - math macro: `"$(" ('exp | 'macro-acceptable)+ "$" 'context ")"`
      - `'context` の仕様は決まってない
    - user macro: `'macro "{" ('exp | 'macro-acceptable)+ "}"`
    - paren: `'parend-exp` ... `"(" 'exp ")"` のこと。
    - pipe: `'exp "|" 'exp` ... `x | f` は `f x` と同じ意味
    - block: `'block`
    - module.access: `'module "." 'name`
  - それ以外
    - sort: `("\PROP" | "\SET" ("(" 'number ")")? | "\TYPE" )`
    - variable: `'variable`
    - depprod.form: `"(" 'variable ":" 'exp ")" "->"  'exp`
    - depprod.intro: `"(" 'variable ":" 'exp ")" "=>"  'exp`
    - depprod.elim: `'exp 'exp`
    - ind.form: `'name`
    - ind.intro: `'name "::" 'name`
    - ind.elim: `"elim" "(" 'name ")" 'exp "return" 'exp "with" ( "|" 'name "(" ('variable ",") ")" "="> 'exp )* "end"`
    - record.form ``'name "(" ('exp ",")* ")"``
    - record.intro: `'name "(" ('exp ",")* ")" "{" "}"`
    - record.proj: `'exp "#" 'name`
    - proof.term: `\Proof 'exp`
    - power.set: `'\Power 'exp`
    - sub.set: `"{" 'variable ":" 'exp "|" 'exp "}"`
    - predicate: `\Pred "(" 'exp "," 'exp "," 'exp ")"`
    - identity: `'exp "=" 'exp`
    - take: `\take 'variable ":" 'exp ( "|" 'exp)?`
    - let: `\let 'variable: ":" 'exp ":=" 'exp "in" 'exp`
- `'block` = `"{" ('block-decl)* 'exp "}" ('where)? ('proof)?`
- `'block-decl` =  either
  - `"fix" ('variable ":" 'exp)+ ";"`
  - `"take 'variable ":" 'exp "|" 'variable ":" 'exp ";"`
  - `"have" 'variable ":" 'exp ":=" 'code-body`
  - `"sufficient" 'exp "by" 'exp;`
- `'where` = `"where" "{" ("-" 'variable ":" 'exp ":=" 'exp ";")+ "}"`
- `'proof` = ` "proof" "{" ("-" "goal" ":" 'exp ":=" 'proof-by ";")+ "}"`
- `'proof-by` = either
  - construct `"\by" 'exp` ... $\Gamma \vdash P$ if $\Gamma \vdash p: P$
  - exact `"\exact" 'exp` ... $\Gamma \vdash \exists A$ if $\Gamma \vdash a: A$
  - subset `"\subelim" 'exp "\in" 'exp "\subset" 'exp` ... $\Gamma \vdash \Pred(A, a, x)$ if $\Gamma \vdash x: \Ty(a, A)$
  - idrefl `"\idrefl" 'exp "\in" 'exp` ... $\Gamma \vdash a = a$ if $\Gamma \vdash a: A$
  - idelim `"\idelim" 'exp "=" 'exp "\with" "(" 'var ":" 'ty ")" "=>" 'exp` ... $\Gamma \vdash (\lambda x: A. P) a_2$ if $\Gamma \vdash a_1 = a_2$, $\Gamma \vdash a_1, a_2: A$, $\Gamma x: A \vdash P_1$, $\Gamma \vdash (\lambda x: A. P) a_1$
  - takeeq `"\takeeq" 'exp "=" 'exp "\with" 'exp` ... $\Gamma \vdash \Take f = t$ if $\Gamma \vdash \Take f, t: X: *^s$
  - axioms = either
    - law of excluded middle `"\axiom:LEM" 'exp ";"`
    - functional extensionality `"\axiom:FE" 'exp "=" 'exp ":" 'exp "->" 'exp`
    - set extensionality `"\axiom:SE" 'exp "=" 'exp "\subset" 'exp `
  - abort: `\abort`

## module
- `'module-decl` = `"module" 'name "(" ('parameter-decl)* ")" ("requires" ('name)+)* "{" ('code-decl)+ "}"`
- `'parameter-decl` = `'variable ":" 'exp`
- `'code-decl` = either
  - `"definition" 'variable ":" 'exp ":=" 'exp`
  - `"theorem" 'variable ":" 'exp ":=" 'exp`
  - `"interpretation" "$(" ('exp | 'macro-acceptable)+ "$)" ":=" 'exp ";"`
  - `"macro"  "$(" ('exp | 'macro-acceptable)+ "$)" ":=" 'exp`
  - `"inductive" 'name ":" ":=" ";"`
  - `"import" 'name "(" ( 'variable ":=" 'exp ) ")" "as" 'name ";"`
  - `"module"`
  - 以降はまだ構文が決まってない部分
    - `"structure"` ... 構造の定義
    - `"property"` ... 構造についての性質の定義
    - `"instance"` ... 構造と集合の結び付けの宣言
    - `"satisfy"` ... 構造が性質を満たすことの宣言と証明
    - `"macro"` ... ユーザーマクロの宣言
- `'code-body` = either
  - `'exp 'where 'proof`
  - `"{" ('block-decl)* 'exp "}" 'where 'proof`
- `'module` = either
  - `'name "(" ('variable ":=" 'exp)* ")"`
  - `'name`
