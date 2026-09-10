# 現状の課題（体系）
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
\[p \leftrightarrow q = (p \to q) \wedge (q \to p) = (c: *^p) \to ((p \to q) \to c) \to ((q \to p) \to c) \to c\]
というふるまいだが、問題はなさそう。

逆はできなさそう。
つまり、 fun ext から set ext は厳しい気がする。
\((\Take x: T. m) = e\) があるので何とかなる気もするが。

## type level equation をどうにかしないといけない
長さ \(n\) の list を作るとして、
- subset と predicate を用いる場合 : \(\{x: \text{List} \mid \text{length} (x) = n\}\)
- 普通の dependent を用いる場合 : `inductive List := | nil: List 0 ; | cons: A -> (n: Nat) -> List n -> List (Nat.succ n)`

前者の場合には、 \(n = m\) から \(l: \Ty (\text{ListLen} (n))\) から \(l: \Ty(\text{ListLen} (m))\) が導出できるが、後者の場合にはできない気がする。
普通は、 \(P: A \to s\) に対して \(x = y -> P x -> P y\) が確かに書けるのでいいが、
（ singleton だから？）
今の状況だと \(P: A \to *^p\) に限定しているのでだめ。

これをどうにかするなら、 TypeLevel での Equal をまずは書けるようにしないといけない。
現状だと \(t_1, t_2: T: *^s_{i}\) じゃないと \(t_1 = t_2\) が書けない。
- まずは \(t_1, t_2: T: s\) に対して \(t_1 =^{s} t_2\) を導入して \(s = *^s\) はいままで通り。

考えたこと：
\(X =^{\sq} Y\) について、
そもそももともとの \(t: \Ty(A, B)\) if \(t: A, \vDash \Pred(A, B)\) についても一般化してしまって、
type level の物に関しては、 \(t: T_1, T_1 =^\sq T_2 \implies t: T_2\) を入れるのはどうか？
これと合わせて、 type level の場合には、「ある種の external なふるまいがあって、それに対して同じようにふるまうのであれば等しい」が入れられればいい。
例えば subset からくる場合は、 \((z: A) \to \Pred(A, x, z) \to \Pred(A, y, z)\) なら \(\Ty(A, x) = \Ty(A, y)\) とする。

これを拡張すると関数のふるまいも同じようにできる気がする。
もともと関数は type level のものなので（ \(X \to Y\) はべき集合 ... \(f: X \to Y\) は subset の同一視だから）、これに対しても external な振る舞いとしての \(f = g\) が \((x: X) \to f x \to g x\) から来ている。
subset の Lift の逆が起きている？
- \(a: A: *\), \(b: \Power A: *\) から \(a: \Ty (A, b): *\) として、 subset は element から type level に引き上げている
- \(f\) はもとから element レベルにいる設定だけど、これが実は type level から来ているものと思える？

これをやり始めたら、結局、 \(*^p\) を impredicative かつ type と同じ階層にいると思って、
\(X \to Y\) と \(X \to *^p\) に対して同じ議論を適用する、そうすると subset と function が両方 extensionality で説明できる？
その話は HOL すぎる？
ちゃんと考察するのが難しい。

- 一般の \(X: K: \sq\) に対して、 \(t: X\) となる"条件" \(\mathbb{P}(X, t)\) がある
- \(\vdash \mathbb{P}(X, t)\) なら \(t: X\) みたいにする？
- \(T_1 =^\sq T_2\) に対する refl: \(P: (X: K) \to *^p\) から \(\vDash P T_1 \to P T_2\)
  - これは、 \(t_1 =^* t_2\) に対する refl: \(P: (X: A) \to *^p \implies \vDash P t_1 \to P t_2\) （ただし \(t_1, t_2: A\) ）から類推した。
- \(\Ty(A, b): *: \sq\) の場合は \(a: \Ty(A, b)\) if \(\vDash \Pred(A, b, a)\) ... \(\mathbb{P}(\Ty(A, b), a) = \Pred(A, b, a)\)
  - \(\mathbb{P}(\Ty(A, \{x: B \mid P\}), a) = (\lambda x: B. P) @ a = P[x := a]\)
- \(P: A \to *^s\) として \(n = m\) から \(\vDash \mathbb{P}(P n, t) \to \mathbb{P}(P m, t)\) 
- subset は \(A \to *^p\) と思えるのは当然だけれど、 \(A\)
- Kind level equality は必要になる？

indexed family を使った場合の type level equalty の話は、
term level の eq から type level の eq を導くのではなく、本当に欲しいのは \(n = m\) から \(T n \to T m\) だと思う。
indexed type family の index が term であること気をつければいい。
あと、これをやるなら prop 側も変えて、 elim と induction を入れる方が綺麗かも。
つまり、 \((A: *^s) \to (a, b: A) \to (p: a = b) \to (P: A \to s) \to P a \to P b\) ができればいい、

この場合には、 computation があるといい？

- \(\text{exp} = (e \text{"="} e) \mid \text{refl}(a) \mid J(A, a, b, p, P, r)\)
- \(J(A, P, r, a, a, \text{refl}(a)) \to r @ a\)
- \(\Gamma \vdash J(A, a, b, p, P, r):\) if
  - \(\Gamma \vdash A: *^s\), \(\Gamma \vdash a, b: A\)
  - \(\Gamma \vdash p: a = b\)
  - \(\Gamma \vdash P: A \to s\) where \(s \in \{*^p, *^s_{i}\}\)
  - \(\Gamma \vdash r: (a: A) \to P a\)

\((p: a = b) \to P a \to P b\) について、 \(*^p\) を一度挟んでいるので、最後の sort が \(*^s\) になっていないのは奇妙に思える。
これを解消するなら \(\exists P a \to \exists P b\) を考えることになるが、
この場合は、 \((a: A) \to \exists (P a)\) に対しての elimination が使えるので、
そもそも書けている。

むしろ、 \(\exists (P a \to P b)\) が一番欲しいものになっていて、
しかも、 computation のことを考えると、 \(\exists (P a \to P a)\) が identity であることがないとめんどくさい。
「この構成によって定義される map が identity であること」を保証するのは、何かしら強力な公理とかを課している？
\((\exists X) \to (\exists Y)\) から \(\exists (X \to Y)\) を取り出すのはやばい気がする。

今気が付いたが、 \(\exists (P a \to P a)\) から \(\exists (P a \to P b)\) が取り出せるから、 id を適用して大丈夫だ。

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
