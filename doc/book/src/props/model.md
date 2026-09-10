# Core calculus の集合モデル

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
ここでは Box-free な raw 項の候補解釈を構成する。
[健全性](soundness.md)は未証明の条件 TC を仮定し、[相対無矛盾性](proof.md)もその条件のもとでのみ得られる。

## 集合論的演算

<a id="universes"></a>

### Universe と trace encoding

外部理論を \(\mathsf{ZFC}\) に次の Grothendieck universe の存在を加えたものとする。

\[
U_i\in U_{i+1}\quad(i\in\mathbb N),\qquad
U_i\in U_\omega\quad(i\in\mathbb N).
\]

\(U_\omega\) は \(\bigcup_iU_i\) という略記ではなく、別の Grothendieck universe である。
各 universe は \(\omega\) を含むものとする。
\(0=\varnothing,\ 1=\{0\},\ \mathbb B=\{0,1\}\) と置く。

任意の集合 \(u,a\) と集合値関数 \(g\) について

\[
\begin{aligned}
\operatorname{app}(u,a)&:=\{z\mid(a,z)\in u\},\\
\operatorname{lam}_A(g)&:=\bigcup_{a\in A}\{a\}\times g(a),\\
\operatorname{Prod}(A,B)&:=
 \{\operatorname{lam}_A(g)\mid g\in\prod_{a\in A}B(a)\}.
\end{aligned}
\tag{Trace}
\]

ordered pair は通常の集合論的 ordered pair である。
app は関数でない集合に対しても定義される。
この関数表現は [Lee–Werner, §3.1, Definition 3.2](https://arxiv.org/pdf/1111.0123)
の trace encoding を用いる。以下の演算補題の証明を明示する。

**補題。**

1. \(a\in A\) なら \(\operatorname{app}(\operatorname{lam}_A(g),a)=g(a)\)。
2. \(u\in\operatorname{Prod}(A,B),a\in A\) なら \(\operatorname{app}(u,a)\in B(a)\)。
3. すべての \(B(a)\in\mathbb B\) について
   \[
   \operatorname{Prod}(A,B)
   =\begin{cases}1&\forall a\in A.\ B(a)=1,\\0&\text{otherwise}.\end{cases}
   \tag{Prop-product}
   \]
4. \(A\in U\)、各 \(B(a)\in U\) なら \(\operatorname{Prod}(A,B)\in U\)。

**証明。** 1 は ordered pair の単射性と外延性。
2 は Prod の witness \(g\) に 1 を適用する。
3 では、空の fiber があれば選択関数が存在しない。
そうでなければ唯一の選択関数は常に \(0\) を返し、その trace は \(0\)。
\(A=\varnothing\) の場合も空関数の trace は \(0\) なので結果は \(1\)。
4 は universe の indexed union、product、powerset、subset に関する閉性：
通常の dependent product を \(U\) 内で作り、その trace の像を取る。□

lambda/application は証明であるかどうかにかかわらず Trace を使う。
とくに \(\operatorname{app}(0,a)=0\)。解釈の定義に導出木や proof/data の分岐は不要である。

<a id="termination"></a>

### 決定的な停止計算

任意の集合 \(A,B,F\) に対し

\[
\begin{aligned}
D_0&=\varnothing,\\
D_{n+1}
&=\{a\in A\mid
 (\exists b\in B.\operatorname{app}(F,a)=(1,b))\\
&\hspace{38mm}\lor
 (\exists a'\in D_n.\operatorname{app}(F,a)=(0,a'))\},\\
D&=\bigcup_{n<\omega}D_n
\end{aligned}
\tag{Finite-accessibility}
\]

と定める。これは任意の集合引数について定義できる。
\(D_n\subseteq D_{n+1}\) は \(n\) の帰納法による。

\(a\in D\) なら、\(a\) から continue を有限回辿り finish に至る。
これは \(a\in D_n\) についての帰納法で得られ、逆も経路長の帰納法で得られる。
二つの停止経路は同じ最初の app 値を持つ。
tag が異なる場合は ordered pair の単射性と \(0\ne1\) に矛盾し、
continue の場合は同じ次状態へ進む。
短い方の経路長に関する帰納法により、終値は一意である。

その終値を \(\operatorname{Run}_{A,B}(F,a)\) とし、\(a\notin D\) なら \(0\) と定める。
また

\[
\operatorname{Case}_{A,B}(F,r):=
\begin{cases}
\operatorname{Run}_{A,B}(F,a')&r=(0,a'),\\
b&r=(1,b),\\
0&\text{otherwise}.
\end{cases}
\]

ここで case の最初の二つの条件は排他的である。

\(F\in\operatorname{Prod}(A,a\mapsto(\{0\}\times A)\cup(\{1\}\times B))\)
の場合、各 \(a\in A\) の app 値は continue または finish のいずれかである。
従って

\[
\begin{aligned}
a\in D
&\Longleftrightarrow
\forall a'\in A.\
  (\operatorname{app}(F,a)=(0,a')\Rightarrow a'\in D),\\
a\in D&\Longrightarrow\operatorname{Run}_{A,B}(F,a)\in B,\\
a\in D&\Longrightarrow
\operatorname{Run}_{A,B}(F,a)
=\operatorname{Case}_{A,B}(F,\operatorname{app}(F,a)).
\end{aligned}
\tag{Run-laws}
\]

第一式の右から左は、finish なら \(D_1\)、continue なら
次状態の属する \(D_n\) の次の段に入ることによる。
左から右も D の定義と決定性による。
第二式は停止経路の終点が B の要素であること、第三式は経路の最初の一歩による。

さらに D は第一式の右辺の演算の最小不動点である。
同演算について閉じた集合 E は、帰納法で全 \(D_n\) を含むからである。
決定的な一後続の計算なので、この構成に超限反復は必要ない。

<a id="interpretation"></a>

## raw 項の解釈

以下の式では可読性のため \(\Pi,\lambda,@\) の rule label を省略するが、
解釈の入力は現行の label 付き構文である。label は集合演算の値には使わない。
これは異なる label の raw conversion を同一視するという意味ではない。
変数 \(x^s\) は項変数と型変数の双方を表す。
\(\square^s_i,\square^p\) への集合の割当ては、判断の sort を解釈するためのものであり、
それらを新しい object term として追加しない。
\(\Take(X,T,f)\) の式は \(\Take^s_i\) と \(\Take^p_i\) の両方に用いる。

valuation \(\rho\) は自由変数に集合を割り当てる。
\(\mathbf t(Q)\) は集合論の命題 Q が真なら 1、偽なら 0 とする。

\[
\begin{aligned}
\llbracket *^s_i\rrbracket_\rho&=U_i,&
\llbracket\sq^s_i\rrbracket_\rho&=U_{i+1},&
\llbracket *^p\rrbracket_\rho&=\mathbb B,&
\llbracket\sq^p\rrbracket_\rho&=U_\omega,\\
\llbracket x^s\rrbracket_\rho&=\rho(x^s),&
\llbracket\Proof P\rrbracket_\rho&=0.
\end{aligned}
\]

以下、右辺の A、S、a、f 等は、対応する構文引数の解釈を表す。
binder を持つ場合は valuation の拡張を明示する。

\[
\begin{aligned}
\llbracket\Pi x:A.B\rrbracket_\rho
 &=\operatorname{Prod}(\llbracket A\rrbracket_\rho,
       a\mapsto\llbracket B\rrbracket_{\rho[x:=a]}),\\
\llbracket\lambda x:A.m\rrbracket_\rho
 &=\operatorname{lam}_{\llbracket A\rrbracket_\rho}
       (a\mapsto\llbracket m\rrbracket_{\rho[x:=a]}),\\
\llbracket f@a\rrbracket_\rho&=\operatorname{app}(f,a),\\
\llbracket\Power A\rrbracket_\rho&=\mathcal P(A),&
\llbracket\Ty(A,S)\rrbracket_\rho&=S,\\
\llbracket\{x:A\mid P\}\rrbracket_\rho
 &=\{a\in\llbracket A\rrbracket_\rho\mid
             \llbracket P\rrbracket_{\rho[x:=a]}=1\},\\
\llbracket\Pred(A,S,a)\rrbracket_\rho&=\mathbf t(a\in S),&
\llbracket a=b\rrbracket_\rho&=\mathbf t(a=b),\\
\llbracket\exists A\rrbracket_\rho&=\mathbf t(A\ne\varnothing),&
\llbracket\Take(X,T,f)\rrbracket_\rho
 &=\bigcup\{\operatorname{app}(f,x)\mid x\in X\},\\
\llbracket\operatorname{RunStep}(A,B)\rrbracket_\rho
 &=(\{0\}\times A)\cup(\{1\}\times B),\\
\llbracket\operatorname{continue}_{A,B}(a)\rrbracket_\rho&=(0,a),&
\llbracket\operatorname{finish}_{A,B}(b)\rrbracket_\rho&=(1,b),\\
\llbracket\operatorname{Acc}_{A,B}(f,a)\rrbracket_\rho&=\mathbf t(a\in D),\\
\llbracket\operatorname{run}_{A,B}(f,a)\rrbracket_\rho
 &=\operatorname{Run}_{A,B}(f,a),\\
\llbracket\operatorname{runCase}_{A,B}(f,a,r)\rrbracket_\rho
 &=\operatorname{Case}_{A,B}(f,r).
\end{aligned}
\]

D は [決定的な停止計算](#termination) の \((A,B,f)\) に対応する集合。
prec の解釈は、r が \((0,a)\) なら \(\operatorname{app}(c,a)\)、
\((1,b)\) なら \(\operatorname{app}(d,b)\)、それ以外なら 0 とする。
motive と型添字は、この場合分けの値には使わない。

これらは項の構造再帰で定義される。
binder の body の評価は、異なる valuation のもとでも真部分項の評価である。
各段の indexed family は置換公理で集合になる。
Run は object term を再帰的に評価する演算ではなく、既に解釈した集合上の [決定的な停止計算](#termination) の演算である。
従って、自由変数に値を与えたすべての raw 項の解釈が存在する。
型の付かない項については、簡約による値の保存を主張しない。

### 意味的代入

\[
\llbracket t[x:=u]\rrbracket_\rho
=\llbracket t\rrbracket_{\rho[x:=\llbracket u\rrbracket_\rho]}.
\tag{Semantic-substitution}
\]

**証明。** t の構造帰納法。変数と sort は定義から従う。
非束縛 constructor は、引数の等しい集合に同じ集合演算を適用するので帰納法から従う。
Proof は両辺 0。prec の motive は値に使わず、他の引数に帰納法を使う。
lambda、product、subset では binder y を \(x,\mathrm{FV}(u)\) と異なる名前にする。
domain の解釈は帰納法で一致し、各 \(a\) について
\(\llbracket u\rrbracket_{\rho[y:=a]}=\llbracket u\rrbracket_\rho\)。
body に帰納法を適用すると indexed family が点ごとに一致する。
よってその trace、product、subset も一致する。□

ここで用いた自由変数以外の valuation に対する不変性も同じ構造帰納法による。
解釈の導出独立性は、補題ではなくこの定義そのものの性質である。
ただし、このことから raw conversion の意味保存は従わない。

<a id="tc"></a>

### Context と未証明の conversion 条件

\[
\begin{aligned}
\operatorname{Val}(\emptyset)&=\{\emptyset\},\\
\operatorname{Val}(\Gamma,x^s:A)
&=\{\rho[x^s:=a]\mid\rho\in\operatorname{Val}(\Gamma),\
                    a\in\llbracket A\rrbracket_\rho\}.
\end{aligned}
\]

この定義は typing soundness を前提としない。空の valuation 集合も許す。

以後の条件付き定理で使う条件は、次の一つである。

\[
\begin{gathered}
\Gamma\vdash_0 T:s,\qquad\Gamma\vdash_0T':s,\qquad T\equiv_0T'\\
\Longrightarrow\
\forall\rho\in\operatorname{Val}(\Gamma).\
\llbracket T\rrbracket_\rho=\llbracket T'\rrbracket_\rho.
\end{gathered}
\tag{TC}
\]

TC の判断は現行体系の判断であり、結論の解釈は [raw 項の解釈](#interpretation)で固定した写像である。
TC 自体を帰納的な規則として体系に追加してはいない。
ここで \(s\in\mathcal S_{sp}\)、\(T,T'\in\mathsf C_s\) とし、
\(\equiv_0\) は現行の同じ構文 family 内の raw conversion を指す。
とくに term typing の型だけでなく、型演算子 typing の kind の conversion も含む。

## 旧記法による検討メモ

以下は、sort による解釈の分岐などを検討していた以前のモデル案である。
上の trace encoding による解釈とは定義が異なり、その健全性の根拠には用いない。
現行 core の定義・証明としては、上の節を参照する。

示したいのは、 Consistency で、「ZFC + いい感じの仮定」のもとでのモデルを作ることで、
\(\vdash \forall P. P\) が示せないことを示す。
これには、 \(\lvert \Vdash (P: *^p) \to P \rvert = \emptyset\) であることを示せばよい。

the not so simple model CoC を参考にする。
次のように定義しておく。
- prop 用
  - \(0 = \bullet = \emptyset\) ... これは、 unique な元として、後述する \(\mathbb{B}\) が Bool っぽくなるようにしている。
  - \(1 = \{ \bullet \}\)
  - \(\mathbb{B} = \{ \bullet, \{\bullet \} \} = \{0, 1\}\)
- \(V_i\): set であって、 inaccessible とかいうやつだが、必要なのは、
  - べき集合で閉じること
  - dependent prod に対応するもので閉じること。
- \(U\): prop の \(\sq^p\) 用。 \((*^s_i, \sq^p, \sq^p)\) があるので、 \(V_i \in U\) である必要がありそう。また、Boolean は含んでいないといけない。

普通のラムダ部分は論文に習えばいい。
ただし、 proof-term かどうかとか、 well-sorted ness を考える必要がある。
（それで定義を分岐するから。）

sort が \((s_1, s_2, s_2) \in \mathcal{R}\) の形なので、 sort-elem function は簡単に定義できる。
ふつうのラムダ以外は決め打ちできるはず。
- \(e(s) = A(A(s))\)
- \(e(x^s) = s\)
- \(e((x: A) \to B) = e(\lambda x: A. B) = e(B a) = e(B)\)
- \(e(\Power A) = \square\)
- \(e(\{A \mid P\}) = *^s\)
- \(e(\Pred(A, B)) = \square\)
- \(e(\Ty(A, B)) = \square\)
- \(e(a = b) = \square\)
- \(e(\exists t) = \square\)
- \(e(\Take f) = *^s\)

これを使って項の属する universe を決め打ちできる。

### 解釈について
\(\Gamma\) と \(t\) に対して、各 集合 \(\lvert \Gamma \Vdash t \rvert _{\gamma}\) を定める。

> [!note]
> 集合論は項が変数のみで、 \(x = y \Leftrightarrow (z \in x \leftrightarrow z \in y)\) をもとに、各集合の記述を項ではなくて命題に任せる。
> だから一回述語論理用の変数の集合 \(\text{Var}\) と、集合論の命題 \(\text{Logic}\) みたいなのがあったときに、
> 集合を与えることは、だいたい \(v \in \text{Var}\) と \(p \in \text{Logic}\) を与えることと同じ。
> この2つを合わせて、 \(x \in v \Leftrightarrow p\) みたいにして集合を記述している。
>
> だからモデルの定義先としての集合を記述する場合、各 hoge に対して \(x \in \text{Var}\) を割り当てつつ、 \(p \in \text{Logic}\) （もしかしたら実は \(x\) に言及していないかもしれない命題） も受け取って、命題（複数の場合は命題の集合集合）を出力する必要がある。

#### 規則

- PTS っぽいところ
  - \(\lvert \Gamma \Vdash *^p \rvert = \mathbb{B}\)
  - \(\lvert \Gamma \Vdash \sq^p \rvert = U\)
  - \(\lvert \Gamma \Vdash *^s_i \rvert = V_i\)
  - \(\lvert \Gamma \Vdash \square^s_i \rvert = V_{i+1}\)
  - \(\lvert \Gamma \Vdash p \rvert = \bullet\)
    - \(\Uparrow\) if \(e(p) = *^p\)
  - \(\lvert \Gamma \Vdash x^\square \rvert _\gamma = \pi_i \gamma\) if \(x^\square\) is \(i\)-th
  - \(\lvert \Gamma \Vdash \lambda x: A. t \rvert _\gamma = \alpha \in \lvert \Gamma \Vdash A \rvert \mapsto \lvert \Gamma; x: A \Vdash t \rvert _{(\gamma, \alpha)}\)
  - \(\lvert \Gamma \Vdash f @ a  \rvert _\gamma = \lvert \Gamma \Vdash f \rvert _\gamma (\lvert \Gamma \Vdash a \rvert _\gamma)\)
  - \(\lvert \Gamma \Vdash (x: A) \to B \rvert = \{f \in \{ \bullet \} \mid \forall \alpha \in \lvert \Gamma \Vdash A \rvert _\gamma , f \in \lvert \Gamma; x: A \Vdash B \rvert _{(\gamma, \alpha)} \}\)
    - \(\Uparrow\) if \(e(B) = \square\)
  - \(\lvert \Gamma \Vdash (x: A) \to B \rvert = \Pi_{\alpha \in \lvert \Gamma \Vdash A \rvert _\gamma} \lvert \Gamma; x: A \Vdash B \rvert _{(\gamma, \alpha)}\)
- ここ以降がちゃんと定義しないといけない部分
  - \(\lvert \Gamma \Vdash \Proof p \rvert _\gamma = \bullet\)
  - \(\lvert \Gamma \Vdash \Power (A) \rvert _\gamma = \mathcal{P}(\lvert \Gamma \Vdash A \rvert _\gamma)\)
  - \(\lvert \Gamma \Vdash \{A \mid P\} \rvert _\gamma = \{x \in \lvert \Gamma \Vdash A \rvert _\gamma \mid \bullet \in \lvert \Gamma \Vdash P \rvert _\gamma (x) \}\)
  - \(\lvert \Gamma \Vdash \Ty(A, B) \rvert _\gamma = \{x \in \lvert \Gamma \Vdash A _\gamma \rvert \mid x \in \lvert \Gamma \Vdash B \rvert _\gamma\}\)
  - \(\lvert \Gamma \Vdash \Pred(A, B, t) \rvert _\gamma = \{a \in \{\bullet\} \mid \lvert \Gamma \vdash t \rvert _\gamma \in \lvert \Gamma \vdash B \rvert \}\)
  - \(\lvert \Gamma \Vdash a = b \rvert _\gamma = \{\bullet \mid \lvert \Gamma \Vdash a \rvert _\gamma = \lvert \Gamma \Vdash b \rvert _\gamma\}\)
  - \(\lvert \Gamma \Vdash \exists t \rvert _\gamma = \{ \bullet \mid \lvert \Gamma \vdash t \rvert _\gamma \not = \emptyset \} \)
  - \(\lvert \Gamma \Vdash \Take f \rvert _\gamma = y \mathrel{\text{s.t.}} \exists x, (x, y) \in \lvert \Gamma \vdash f \rvert _\gamma\)
    これの型が \(X \to Y\) なら \(f \subset X \times Y\) なのでこう書けるはず。
    \(\text{s.t}\) の意味が不明瞭に見えるけれど、そもそも集合自体、自由変数で導入した後に論理式で定義を用いるのでよい。
    （ \(z \in \{y \in x \mid \phi(y, x)\}\) が \((k \in l \leftrightarrow \phi(y, k)) \rightarrow z \in l\)  になるのと同じ。）

> [!note]
> AI による指摘： mal-formed なものに対してもうまく take が定義されてほしいので、 \(\lvert \text{Take}(X, T, f) \rvert = \bigcup_{x \in X} f(x)\) にするとよいらしい。
> 同じようなもんだと思うが。

subst は大丈夫だと思うので飛ばす。
reduction に対してどうふるまうかがみたい。
congruent な部分はだいたい大丈夫なはずで、問題は reduction のあるところ。
ラムダの話は 『not so simple ..』 にのってる。
- \(M = (\lambda x^s: A. t) @ u \to t[x := u]\) の場合：
  - \(e(M) = *^p\) の場合には、 \(s = *^p\) のはずで、 \(\lvert A[x^{*^p} := u] \rvert = \lvert \Gamma; x: t \vdash A \rvert _{(\gamma, \lvert u \rvert)}\) が subst からわかる。
  - \(e(t) = *^p\) だが \(e(M) \not = *^p\) なら、これも同様の議論
  - どちらでもない場合には、これは function になっている。
- \(M = \Pred(A, \{x: B \mid P\}, t) \to_\beta (\lambda x: B. P) @ t\) の場合：
  - \(\lvert \Pred(A, \{x: B \mid P\}, t) \rvert\)
    - ... \(\{a \in \{\bullet\} \mid \lvert \Gamma \vdash t \rvert \in \lvert \Gamma \vdash \{x: B \mid P\} \rvert\}\)
    - ... \(\{a \in \{\bullet\} \mid \lvert t \rvert \in \lvert B \rvert \wedge \bullet \in \lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}\}\)
  - \(\lvert \Gamma \vdash (\lambda x: B. P) @ t \rvert\)
    - ... \((\alpha \in \lvert B \rvert \mapsto \lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \alpha)}) (\lvert t \rvert)\)
    - ... \(\lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}\)
  - \(\lvert \Gamma; x: B \vdash P \rvert _{(\gamma, \lvert t \rvert)}\) が定義されている時点で、
    \(\lvert t \rvert \in \lvert B \rvert\) になっているはずなので、
    これを踏まえると、 \(\{\bullet\} \cap\) が後者につけれれば、集合として同じになる。

well-sorted の定義の時点で \(\Pred(A,B,t)\) には条件を付けてしまえば、次のような**感じ**の定理が証明できると思われる。
> \(t \to t'\) かつ \(t\) は well-sorted とする。
> このとき、 \(t'\) も well-sorted であり、 \(s(t) = s(t') =: s\) が成り立つ。
> また、 \(\lvert \Gamma \Vdash t \rvert \cap \lvert s \rvert = \lvert \Gamma \Vdash t' \rvert \cap \lvert s \rvert\) が成り立つ。
