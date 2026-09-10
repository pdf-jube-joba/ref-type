# Core calculus の typing

対象は [system.md](../system.md) の、Box と datatype 宣言を除いた Set/Prop core である。
現行の kind formation、型演算子 typing、項 typing、provability と WF を扱う。
\(z^\sigma\) は、\(\sigma=b\) なら項変数、\(\sigma=\kappa(b)\) なら型変数を表す。
rule label と構文 family は各導出で保持する。

## Weakening と substitution

**補題（weakening）。** context の順序を保って fresh な宣言を挿入し、
その結果が well-formed なら、その context への全判断の weakening は許容的である。

**証明。** 五判断の導出について同時帰納する。
variable の宣言より後に挿入するときは weak を使い、
前に挿入するときは挿入後の context で variable を使う。
start は型・kind の formation に帰納法を使う。
他の規則では局所 binder を fresh に取り直し、全 premise に同じ挿入を行う。
conversion の raw equality は context を参照しない。
provability には provable weak または各規則の再適用を使う。
free-variable の side condition は fresh な名前の選択で保存される。□

**補題（substitution）。** \(J\) を kind formation、型演算子 typing、項 typing、
provability のいずれかとする。
\[
\begin{gathered}
\Gamma,z^\sigma:A,\Delta\vdash J,\qquad \Gamma\vdash u:A\\
\Longrightarrow
\Gamma,\Delta[z:=u]\vdash J[z:=u].
\end{gathered}
\tag{Substitution}
\]
WF についても
\[
\operatorname{WF}(\Gamma,z^\sigma:A,\Delta),\quad\Gamma\vdash u:A
\Longrightarrow\operatorname{WF}(\Gamma,\Delta[z:=u])
\]
が成り立つ。代入は後続 context の型・kind と構文中の注釈にも作用する。

**証明。** 五判断の導出について同時帰納する。
代入項と変数は同じ \(\mathsf E_\sigma\) に属するため構文 family が保存され、
rule label は代入で変化しない。

- variable が \(z\) なら \(u\) の導出を後続 context へ weakening する。
  他の変数なら、代入後の宣言を variable と weak で取り出す。
- empty と axiom は変化しない。start/weak で \(z:A\) 自身を追加する段は削除し、
  他の宣言は帰納法で得た formation を用いて再構成する。
- conversion の三つの typing/formation premise に帰納法を使う。
  raw beta の代入保存は[代入の合成則](metatheory.md#substitution)、
  Pred、prec、run、runCase は同じ metavariable への一様な代入による。
  重複した型添字にも同じ代入をするので root の一致条件は保存される。
  compatible closure と有限 zigzag へ拡張すれば conversion の側条件も保存される。
- dep form/intro/elim、subset form、id elim、prec、acc intro では、
  局所 binder を fresh に取り直して premise に帰納法を使う。
  結論や branch 型に現れる二重の代入は代入の合成則で交換する。
- power set form、type lift、predicate、subset intro/weak/prop、
  id form/intro、exists form/intro、両 take elim、take equal、
  RunStep formation と constructor、acc form/descent、run/runCase、
  provable と proof term は、全 premise に帰納法を使って同じ規則を適用する。

take の定値性の premise にも代入が作用する。
すべての再帰呼び出しは元の導出の真部分木に対するものである。□

<a id="regularity"></a>

## Regularity と命題の conversion

**補題（Regularity）。**
\[
\begin{aligned}
\Gamma\vdash J\text{ または }\Gamma\vDash P
 &\Longrightarrow\operatorname{WF}(\Gamma),\\
\Gamma\vdash t:A,\quad t\in\mathsf{Tm}_b
 &\Longrightarrow\Gamma\vdash A:b,\\
\Gamma\vdash A:K,\quad A\in\mathsf{Ty}_b
 &\Longrightarrow\Gamma\vdash K:\kappa(b),\\
\Gamma\vDash P&\Longrightarrow\Gamma\vdash P:*^p.
\end{aligned}
\tag{Regularity}
\]

**証明。** WF は規則の共通 premise である。残りは導出の同時帰納法。
variable は宣言を追加した start の formation を weakening する。
conversion は目標の formation premise、weak は帰納法による。
dep intro の結果型は dep form、dep elim と prec の結果型は Substitution で形成する。
型・項の他の導入規則は、表示された formation premise に対応する formation 規則を使う。
subset intro の結果型は type lift、subset weak と run/runCase は formation premise そのもの。
take elim の結果型の formation も明示されている。

provable には \(P:*^p\) の premise があり、proof term には provability の帰納法を使う。
subset prop、id intro、exists intro、acc intro/descent は対応する formation である。
take equal は Take と application を同じ \(T\) で型付けして id form を使う。
id elim の結論は \(p_i=(*^s_i,\square^p,\square^p)\) による
型演算子の dep intro/elim で \(*^p\) に型付けできる。□

従って
\[
\Gamma\vDash P,\quad\Gamma\vdash Q:*^p,\quad
P\equiv_{\mathsf{Ty}_{*^p}}Q
\Longrightarrow\Gamma\vDash Q.
\tag{Prop-conversion}
\]
証明は proof term、conversion、provable の順の適用である。
conversion に必要な \(P:*^p\) は Regularity から得る。

## Context conversion

**補題。** \(\Gamma\vdash A:\sigma\)、\(\Gamma\vdash A':\sigma\)、
\(A\equiv_{\mathsf C_\sigma}A'\) とする。
\[
\Gamma,z^\sigma:A,\Delta\vdash J
\Longrightarrow
\Gamma,z^\sigma:A',\Delta\vdash J.
\tag{Context-conversion}
\]
WF に対しても同じ置換が許容的である。

**証明。** \(y^\sigma\) を全自由変数と異なる名前に取る。
\(\Gamma,y:A'\) は well-formed であり、
variable、weakening、conversion により \(\Gamma,y:A'\vdash y:A\)。
元の導出に \(y:A'\) を \(z:A\) の直前で挿入する。
Substitution で \(z\) に \(y\) を代入すると
\(\Gamma,y:A',\Delta[z:=y]\vdash J[z:=y]\) を得る。
最後に \(y\) を \(z\) に名前替えする。WF も同じ操作による。
この証明は subject reduction も集合モデルも使わない。□

<a id="subject-reduction"></a>

## Subject reduction の到達点

<a id="principal-root"></a>

### Principal root の保存

ここで principal とは、消去規則に渡す constructor の typing が対応する導入規則で終わり、
導入・消去の型、motive、rule label が表示どおり一致する場合をいう。

- beta：lambda の body typing に Substitution を適用する。
- Pred/subset：subset form の \(P:*^p\) に、rule label \(p_i\) の
  型演算子の dep intro を適用する。引数 \(t:B\) が与えられていれば、
  dep elim で reduct を \(*^p\) に型付けできる。
  ここでは外側の predicate が要求する \(t:A\) だけから \(t:B\) を推論していない。
- prec/continue と prec/finish：constructor の argument typing と
  branch の typing に dep elim を適用する。motive の代入が結果型になる。
- run：dep elim で \(f@_{s^{i,i}}a:\operatorname{RunStep}(A,B)\)。
  id intro による自己等号と元の Acc premise を合わせ、runCase を適用する。
- runCase/continue：constructor の argument typing と、
  元の Acc・equality premise に acc descent を適用して後続の Acc を得る。
  run により reduct を \(B\) に型付けする。
- runCase/finish：constructor の premise がそのまま reduct の \(B\) での typing である。

これらは有限導出の明示的な構成である。

### 一般形に残る問題

目標は、各 Set/Prop family の compatible reduction に対する
\[
\begin{aligned}
\Gamma\vdash e:A,\quad e\Rightarrow_0e'
 &\Longrightarrow\Gamma\vdash e':A,\\
\Gamma\vdash K:\kappa(b),\quad K\Rightarrow_0K'
 &\Longrightarrow\Gamma\vdash K':\kappa(b).
\end{aligned}
\tag{SR}
\]
provability の保存は、命題の typing の SR と Prop-conversion から得られる。

Context-conversion は上で証明した。しかし、元の \(\equiv_0\) を使う体系では、
constructor の typing が conversion、subset intro/weak、weak を経由した場合の generation はまだ必要である。
補助 conversion を使う \(\mathcal S_+\) については、
[refinement root による generation](generation.md#generation)でこの部分を証明した。
とくに \(t:A\) と \(t:\Ty(A,S)\) の両方が導出できるため、
通常の PTS の型の一意性をそのまま使えない。
必要なのは、消去規則の表示型で body/argument の typing を回収する補題である。
Pred/subset についても、内側の domain \(B\) での引数 typing を回収する必要がある。

さらに binder 内の簡約、subset prop の移送、重複した型添字の一方だけを
簡約した場合を含めて compatible closure を扱う必要がある。
[補助 reduction の共通簡約先](confluence.md#auxiliary-reduction)は、
その共通簡約先の typing や元の reduction の合流性までは与えない。
同ページの補助関係は現行の family と rule label を保持するが、
そのことだけでは typing の保存は得られない。

[条件 TC](model.md#tc)の証明には、さらに[意味保存](soundness.md#tc-obligation)が必要である。
上の構文的補題だけから、一般の SR や TC を証明済みとは結論しない。

一方、[補助体系の SR](subject_reduction.md#sr-plus) は、
generation を用いて compatible closure と provability まで含めて証明できる。
元の体系の導出は補助体系にも移せるので、無矛盾性を補助体系で示す経路がある。
この場合に残るのは、同ページの Semantic-step-plus である。

## 旧記法による検討メモ

以下は、以前の記法・規則に基づく導出の検討を保存したものである。
現行 core の定義・証明としては、上の節を参照する。

体系の judgement が 4 つあって相互再帰的に定義されているから、大体の命題も、相互再帰的に定義するしかない。

### free variable について
> - \(\text{WF}(x_1: A_1:: \cdots :: x_n: A_n)\) なら \(x_i\) はすべて異なり、 \(\text{FV}(A_i) \subset \{x_1, \ldots, x_{i-1}\}\)
> - \(\Gamma \vdash^s t: T\) なら \(\text{FV}(t), \text{FV}(T) \subset \Gamma\)
> - \(\Gamma \vdash t: s\) なら \(\text{FV}(t) \subset \Gamma\)
> - \(\Gamma \vDash P\) なら \(\text{FV}(P) \subset \Gamma\)
- 証明は、導出木に関する帰納法を用いる。

### variable の導出
> \(\text{WF}(\Gamma)\) かつ \((x: T) \in \Gamma\) なら \(\Gamma \vdash x: T\)

証明：
\(\text{WF}(\Gamma)\) は empty と start のみから導出されているので、
\(\Gamma = \Gamma_1 :: (x: T) :: \Gamma_2\) に対して \(\text{WF}(\Gamma)\) の導出木を分析すれば、
\(\Gamma_1 \vdash T: s, x \notin \Gamma \implies \text{WF}(\Gamma_1::(x:T))\) の部分があるはず。
ここから、 \(\Gamma_1 :: x: T \vdash x: T\) が示せて、あとは weak を \(\Gamma_2\) に合わせて広げていくだけ。

### substitution lemma
> \(\Gamma \vdash t: T\) とする。
> - \(\text{WF}(\Gamma:: x: T::\Gamma')\) なら \(\text{WF}(\Gamma::(\Gamma'[x := t]))\)
> - \(\Gamma:: x: T::\Gamma' \vdash^s M: N\) なら \(\Gamma::(\Gamma'[x := t]) \vdash^s M[x := t]: N[x := t]\)
> - \(\Gamma:: x: T::\Gamma' \vdash M: s\) なら \(\Gamma::(\Gamma'[x := t]) \vdash M: s\)
> - \(\Gamma:: x: T::\Gamma' \vDash P\) なら \(\Gamma::(\Gamma'[x := t]) \vDash P[x := t]\)

Note:
\(\vdash M: N\) のときの \(\Gamma' = \emptyset\) でその導出が var のときが base case である。
\(\Gamma :: x: t \vdash x: t\) if \(\text{WF}(\Gamma)\) なので、この場合、 \(\Gamma \vdash x[x := t]: T[x := t]\) を示すが、これは前提の \(\Gamma \vdash t: T\) である。

証明：
\(\Delta = \Gamma :: x: T :: \Gamma'\), \(\Delta^* = \Gamma:: \Gamma'[x := t]\) とする。

各結論の前提（ 「hoge なら huga」 の hoge の部分）の導出木に関する帰納法を用いる。
この議論はちょっとわかりにくいので補足する。
\(\Gamma, t, T, x\) は固定する。
context \(\Gamma'\) についての命題が「 \(\Gamma::x: T::\Gamma'\) についてのそれぞれの命題の導出木 \(D\) （相互再帰がここで入る）」
をもとに \(P(\Gamma') = \forall D. Q(\Gamma', D)\) として得られていると思えば、この導出木に関する帰納法が使えるということ。
（導出木の長さに関する帰納法を用いていると思ってもいいかも）

- empty, axiom の場合 ... 明らか。
- start の場合 ... \(\Delta = \Delta':: x': T'\) によって \(\text{WF}(\Delta'::x': T')\) if \(\Delta' \vdash T': s'\), \(x \notin \Gamma\) が成り立っている。
  - もし \(\Delta' = \Gamma\) なら（つまり \(\Gamma' = \emptyset\)）：これはまさに Note で書いた base case である。
  - そうじゃないなら、帰納法の仮定から、 \(\forall D'. P(\Delta', D')\) が帰納法の仮定から得られているので、
    \(\Gamma::\Delta'[x := t] \vdash T'[x := t]: s\) がわかっている。
    ここの仮定から \(\text{WF}(\Gamma::\Delta'[x := t]::x': T'[x := t])\) が得られるから、示すべきことが示されている。
- weak の場合 ... (start と同じようなもの) \(\Delta = \Delta':: x': T'\) によって \(\Delta'::x': T' \vdash M: N\) if \(\Delta' \vdash M: N, \text{WF}(\Delta'::x':T')\) が成り立っている。
  - もし \(\Delta' = \Gamma\) なら （つまり \(\Gamma' = \emptyset\)）： \(\Gamma \vdash M: N, \text{WF}(\Gamma \vdash x: T)\) から
    \(\Gamma ::x: T \vdash M: N\) を導出している。
    示すのは \(\Gamma \vdash M[x := t]: N[x := t]\) であるが、 \(x \notin \text{FV}(M), \text{FV}(N)\) がわかるから、これは \(\Gamma \vdash M: N\) になり、示されている。
  - そうじゃないなら、帰納法の仮定から、 \(\Gamma ::\Delta'[x := t] \vdash M[x := t]: N[x := t]\) と \(\text{WF}(\Gamma ::\Delta'[x := t]::x': T'[x := t])\) が得られているから、そのまま \(\Gamma::\Delta'[x := t]::x': T'[x := t] \vdash M[x := t]: N[x := t]\) の導出木にできる。
- conversion の場合 ... premises に現れる context が減ってないので、帰納法の仮定から得られるものをそのまま適用すればいい。
  これがわかりやすいので、ちゃんと書いてみる。
  \(\Gamma:: x: t :: \Gamma' \vdash t': T_2\) if \(\Gamma::x:t::\Gamma' \vdash t': T_1, \Gamma::x:t::\Gamma' \vdash T_2: s, T_1 \equiv T_2\) と導出されていて、
  帰納法の仮定から \(\Gamma::\Gamma'[x:=t] \vdash t'[x:=t]: T_2[x:=t]\) と \(\Gamma::\Gamma'[x:=t] \vdash T_2[x:=t]:(s[x:=t] \equiv s)\) が得られている。
  これをそのまま導出木にしてしまえばいい。チェックするのは、 \(T_1[x:=t] \equiv T_2[x:=t]\) だがこれは成り立つ。 
- variable, dep.form, dep.intro, provable list, power-sub list, set-rel list, identity list の全部、 exists intro exist form では上と同じ議論が使える。
- dep.elim の場合：
  \(\Delta \vdash f @ a: T[x' := a]\) if \(\Delta \vdash f: (x': t'. a), \Delta \vdash a: t'\) としておく。
  示すのは \(\Delta^* \vdash (f @ a)[x := t]: T[x' := a][x := t]\) だが、
  これは代入順序の補題を用いれば \(\Delta^* \vdash (f[x := t] @ a [x := t]): T[x := t][x' := a[x := t]]\) と同じなので、
  帰納法の仮定の \(\Gamma' \vdash f[]: ()[], \Delta \vdash a[]: t'[]\) から導出できる。
- take.intro. の場合：
  \(\Delta \vdash (\Take x': T'. m): M\) if \(\Delta \vdash T': *^s, \Delta \vdash M: *^s, \Delta ::x': T' \vdash m: M, \Gamma \vDash \exists T', \Gamma \vDash (y_1: T') \to (y_2 : T') \to m[x := y_1] =_M m[x := y_2]\) からきているとする。
  （ \(x'\) は \(t\) に出現しないような変数。）
  示すのは \(\Delta \vdash (\Take x': (T'[x := t]).(m[x := t])): M[x := t]\) なので、
  まずは帰納法の仮定から得られる、 premise それぞれに \([x := t]\) を付けたものを考える。
  そこから自然に得られる導出木はほとんど気にしなくてよくて、 \(\Gamma \vdash (y_1: T'[]) \to (y_2 : T'[]) \to m[x' := y_1][x := t] =_M m[x' := y_2][x := t]\) だけ気にしないといけない。
  ただこれは、代入順序の補題から、 \(\Gamma \vdash \cdots m[x := t][x' := y_1] =_M m[x := t][x' := y_2]\) とできるからよい。
- take.elim （ bind あり）の場合：
  これも気にするのは、 \( \cdot =_M m[x' := e]\) の代入の順番であるが、 \(m[x' := e][x := t] = m[x := t][x' := e[x := t]]\) よりよい。

### generation lemma (inversion)
#### sort まわり
> - \(\Gamma \not \vdash \square:  s\)
> - \(\Gamma \vdash *^p: s\) なら \(s = \square\)
> - \(\Gamma \vdash *^s_i: s\) なら \(s = *^s_{i+1}\)
- 証明は普通に木を見ればいい。

> - \(\Gamma \not \vdash^s \square: T\) 
> - \(\Gamma \not \vdash^s *^p: T\)
- これも同じ。 type.elem では上の命題から。

> \(\Gamma \vdash^s *^s_i: T\) なら \(s = *^s_{i+2}\)

#### type になれない項
> - \(\Gamma \not \vdash (\lambda x: T. t): s\)

#### lambda まわり
> \(\Gamma \vdash^{s_3} (\lambda^{s_1} x: B. t): T_2\) かつ \(T_2 \equiv (x: B') \to T\) なら \(B \equiv B'\) かつ \(\Gamma; x: B \vdash^{s_2} t: T\)

#### sort には prop goal が発生しない？
> \(\Gamma \vdash t: s\) の導出木には \(\Gamma \vDash P\) の形が発生しない。
