> このページは体系と構文の検討記録です。現行の仕様は [体系](../system.md) と [表面構文](../language/syntax.md) を参照してください。

# 体系の検討記録
## ideal な世界としての computation や template 用の universe ?
次の問題は全部、ある種の computation 用の sort を用意しておいて、
そこの世界の template としての項を、
（条件付きで）持ってきてよいという感じに考えた方がよさそうに思えた。
つまり、理想的な記述の仕方（普通に矛盾しうる世界）を考えて、
それが well-grounded(?) なら Set 側の項として実現してよい。

### universe level polymorphism について
構造として \(X: U_i\), \(\mu: X \times X \to X\) の組を考えてみる。
このとき \((X, \mu): (X: U_i) \times (X \times X \to X): U_{i+1}\) のようになるが、
このレベルが上がるのは仕方がない。
（これをやるにはさらに \((U_{i+1}, U_i, U_{i+1}) \in \mathcal{R}\) とか cumulative （\(T: U_i \implies T: U_{i+1}\)）が必要になるが、そこは本題じゃない。）
理由は、「台集合 \(\subset *^s_i\) とその上の二項演算の組」の集合を考えればそれが \(U_i\) には入らないのは当然だから。
ただここでの問題は、そうなると、定義を universe ごとに繰り返さなければいけないこと。
例えば群を例にすれば、 \(U_{0}, U_{1}, U_{2}\) それぞれで帰納的な型やレコード型として定義する必要がある。
これはめんどくさいので、 universe level を受け取っての定義ができるとうれしいが、もっと根本的に解決できないか。

### decidable について
Rocq だと decidable は \(P \vee \neg P\) として定義されているけど、 排中律を公理に入れたときに、相性がよくない。
排中律自体はほしいが、 decidable の意味合いを壊したくない。
なので、 \(*^p\) ではないところに2値の Bool 型をもっておくのがいいかも。
Bool 型を用いて \(f: X \to \text{Bool}\) と \(p: X \to *^p\) がいい感じになっていたとき、ある程度の範囲では自動的に Prop を計算できたらうれしい。
ただし、 \(*^s\) のところに入れるとそのまま影響されてしまうことになりそうなので、
これも、 description 用の universe としての \(*^s\) ではない、 computation 用の universe としての \(*^c\) を用意してそこで定義するのがいいかも。

例として、 \(3 < 5\) は計算できるはず。
なので、 `leq 3 5` を見たときに `by leqb 3 5` と簡単に結び付けられるといい。
つまり、 `leq` と `leb` を自動で補完する？
これをやるにはそもそもなにか結び付けを宣言する機構が必要になるので、やめたほうがいいかも。

## \(\exists\) について
\(\exists T\) という項を導入したけれど、これは新たに導入せずに CoC の impredicative encoding の話が使うこともできそう。
CoC だと、 \(A: *\), \(P: A \to *\) に対して、 \(\exists x: A. P := \forall (C: *), (C \to) \to ... \)
ただし、 first projection は定義できても second projection はいい感じのものにならない。
これは使える？

現状だと、 \(\exists\) は \(\Take\) を elim に持つようになっていて、強い結びつきがあるから、これを壊さないようにしたい。

## fun ext をどうにかして導出できないか？
これは現状ではできなそう。
\(X, Y: *^s\) と \(f, g: X \to Y\) を用意して、 \(p_{f = g}: (x: X) \to f x = g x\) としておく。
（ここは依存型でもいい。）
このときに \(f = g\) がほしい、という話。

### 関係としての関数：
関係としての関数： \(R: (x: X) \to (y: X) \to *^p\) であって、次を満たすもののことを考えている。
1. \(p_1: (x: X) \to \exists \{y: Y \mid R x y\}\) 
2. \(p_2: (x: X) \to (y_1, y_2: Y) \to R x y_1 \to R x y_2 \to y_1 = y_2\)

ここから関数を取り出すとすると、 \(\lambda (x: X). \Take \{y: Y \mid R x y\}\) がちゃんと \(X \to Y\) に型付けされる。
だから関数は取り出せている。
これを \(\text{Func}(R)\) と書いておく。
これを考えると、 \(f: X \to Y\) に対して、 "unique に定まる" proposition からの取り出しができる。
つまり、 \(R_f := (x: X) \to (y: Y) \to f x = y\) とすることで \(f \mapsto \text{Func}(R_f)\) ができる。

\(R_f, R_g\) は関係なので、 \(R_f = R_g\) を書くことができない。
かわりに、 \((x: X) \to (y: Y) \to (R_f x y \Leftrightarrow R_g x y)\) はできる。
（\(p_{f = g}\) から \(f x = y \Leftrightarrow g x = y\) が示せるから。）

\(\text{Func}\) 自体の考察：
\(\text{Func} := (X, Y: *^s) \mapsto (R: X \to Y \to *^p) \mapsto (p_1: (x: X) \to \exists \{y: Y \mid R x y\}) \mapsto (p_2: (x: X) \to (y_1, y_2: Y) \to R x y_1 \to T x y_2 \to y_1 = y_2) \mapsto (x: X) \mapsto \Take \{y: Y \mid R x y\} \) で、
これの型は \((X, Y: *^p) \to (R: X \to Y \to *^p) \to (\text{map all}) \to (\text{map unique}) \to X \to Y\) になっている。

### 集合としての関数：
集合論的には \(X \times Y\) の部分集合のことになっている。
dependent でない sum は扱いがある程度楽だった気がする。
確か、 impredicative な encoding のもとで \(A \times B := (C: *) \to (A \to B \to C) \to C\) だった。
ただ、帰納型でやるにせよ encoding を使うにせよ、\(*^p\) と \(*^s\) のどっちに属するのかを考えないといけないが、今はこの話をちょっと置いておく。

\(\{z: X \times Y \mid f (\pi_1 z) = \pi_2 z\}\) が \(f\) のグラフを表している。
\(\{z: X \times Y \mid f (\pi_1 z) = \pi_2 z\}, \{z: X \times Y \mid g (\pi_1 z) = \pi_2 z\}\) はともに \(\Power (X \times Y)\) の元。
（type のレベルじゃなくて term のレベルにある。）
これが \(=\) であることは示せなさそう。

集合的な外延性が必要？
\(X: *^s, Y_1, Y_2: \Power(X)\) に対して、 \(((z: X) \to (\Pred(X, Y_1, z) \Leftrightarrow \Pred(X, Y_2, z))) \implies Y_1 = Y_2\) が axiom として入っているとする。
これなら確かに、 \(\{\} = \{\}\) は成り立つ。

成り立つとしても、ここから \(f = g\) は取り出せない。

### その他考察
extensionality は項の (propositional な) uniqueness が、外部との関連から導き出せる話になっている。
\(x, y: X: *^s\) に対して、\(X\) という型の性質から定義される相互作用のようなものに対して、 \(x\) と \(y\) の振る舞いが同じなら \(x = y\) みたいな感じ。
- set ext: \(X: *^s, Y_1, Y_2: \Power (X) \vDash ((z: X) \to (\Pred(X, Y_1, z) \leftrightarrow \Pred(X, Y_2, z)))  \to Y_1 = Y_2\)
- fun ext: \(X: *^s, Y: *^s, f_1, f_2: X \to Y \vDash ((x: X) \to f_1 x = f_2 x) \to f_1 = f_2\)

これの見方として、 \(Y_1, Y_2\) を \(X \to *^p\) のことだと思えば、
Coq の Prop ext （\(*^p\) にも \(=\) があって \((p \leftrightarrow q) \to (p = q)\)） を仮定すれば、 set ext は fun ext になる。
（ fun ext でいう \(Y\) を \(*^p\) にして、 \(\Pred(X, Y_i, z)\) は \(Y_i z\) になっている。）
ちゃんと \(\leftrightarrow\) を考えると、
\[p \leftrightarrow q = (p \to q) \wedge (q \to p) = (c: *^p) \to ((p \to q) \to (q \to p) \to c) \to c\]
というふるまいだが、問題はなさそう。

逆はできなさそう。
つまり、 fun ext から set ext は厳しい気がする。
\((\Take x: T. m) = e\) があるので何とかなる気もするが。

## 導出木と \(\vDash\) について
type level の話を書いていて、（当然だけど）
結論に \(\vDash\) が来る規則は、全部上側に型チェックが来るようにできる。
（上側の \(\vDash\) を下に持ってきて mp にすればいいから）

## global choice について
\(\exists X\) を \(\lvert X \rvert\) と書くことにする。
classical indefinite choice として \(((x: A) \to \lvert B \rvert) \to \lvert (x: A) \to B \rvert\) があってもいいと思った。

ライブラリとして関数外延性や集合外延性と同様に axioms みたいなものを作ってそこに入れてもよさそう。

uniqueness の方があると extensionality が示せそう？
\(x, y: X\) なら \(x = y\) が示せるのが uniqueness だが、性質としては subsingleton というらしい。
subsingleton (\(\text{SS}(X)\)): \((x: X) \to (y: X) \to *\) := \((x: X) \Rightarrow (y: X) \Rightarrow x = y\) とする。
\((x: A) \to B(x)\) に対して \((x: A) \to \text{SS}(B(x))\) から \(\text{SS}((x: A) \to B(x))\) をえる操作があるとどうなる？

これはほぼ funext だったらしい。

## Carrier 上の Relation 全体が書けない
`\definition Relation(Carrier: \Set): _ := Carrier -> Carrier -> \Prop;`
これは定義できない。
`Carrier: \Set |- Carrier -> Carrier -> \Prop: \PropKind` なので、 module parameter みたいに context に push するものはうまくいく。
ただしここから pop しようとするとだめで、
`|- (Carrier: \Set) => Carrier -> Carrier -> \Prop): (Carrier: \Set -> \PropKind)` に対して `Carrier: \Set -> \PropKind` の型がないといけない。
`\PropKind` は最上位なので作れない。

AI の提案の `\alias Relation[Carrier: \Set]: _ := Carrier -> Carrier -> \Prop;` はよさそう。

> [!note]
> 例えば単純型付き言語に List を入れるとして、 `List[Nat]` とか `List[List[A]]` みたいなのは書いていいが、
> `List` が型から型への関数とは思わない、みたいな感じ。
> すでに帰納型では似たような仕組みとして、 parameter と index の区別がある。

## Relation と RelationAsPowerSet の変換ができない
```
\definition RelToPair(A: \Set) (R: Relation[A]): RelPair A := { x: Pair.Times^[A, A] \where R (fst A x) (snd A x) };
```
`A: Set, R: A -> A -> Prop |- { x: A times A | R (fst x) (snd x) }: Pow(A times A): Set` はできる。
これを pop する場合 `|- (A: Set) => (R: A -> A -> Prop) => { x: A times A | ... }: (A: Set) -> (R: A -> A -> Prop) -> Pow(A times A)` となって `(A: Set) -> (R: A -> A -> Prop) -> Pow(A times A)` の sort が問題になる。

(Prop, Set, Set) 則を認めること自体は、集合モデルだと妥当だが、
帰納型がある状況だと proof の詳細を外部に漏らしうる気がする。

## 問題になるかどうかわからんが型の transport ができてる。
```
\definition ready: \RunStep[AddState^, Nat^] -> \Prop :=
  \step-match t: \RunStep[AddState^, Nat^] \return \Prop \with {
    | \continue s: \Acc[AddState^, Nat^](AddLoop::[step]^, s)
    | \finish result: L.True
  };
\definition accIntro (s: AddState^) (certificate: ready (AddLoop::[step]^ s)):
  \Acc[AddState^, Nat^](AddLoop::[step]^, s) :=
  \accintro[AddState^, Nat^](AddLoop::[step]^, s,
    \fun (next: _) (edge: _) =>
      \idelim AddLoop::[step]^ s = \continue[AddState^, Nat^](next)
        \with t: \RunStep[AddState^, Nat^] => ready t
        \by { base: certificate, equality: edge });
```

これは `ready (\continue s) = Acc[], ready (\finish r) = L.True` と `edge: step s = continue(next)` から
型の間の transport をしていることになる。つまり、 `finish r = continue r -> Acc[] -> L.True` を使っている。
これ自体は `x = y -> P(x) -> P(y)` が作れることを認めているのでいいが、ちょっと怖いかも？
