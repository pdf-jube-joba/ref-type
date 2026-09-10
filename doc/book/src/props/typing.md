# Core calculus の typing

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。

## 導出についての基本補題

ここでは \(\mathcal S_0\) を扱う。代入は context の後続の宣言にも作用する。
raw 代入の合成則は [構文的補題の代入の合成則](metatheory.md#substitution) を使う。

### Weakening と substitution

\(J\) は sorting、typing、provability のいずれかとする。

\[
\begin{gathered}
\Gamma\vdash J,\quad \operatorname{WF}(\Gamma,\Delta)
\ \Longrightarrow\ \Gamma,\Delta\vdash J,\\
\Gamma,x^s:A:s,\Delta\vdash J,\quad\Gamma\vdash u:A:s
\ \Longrightarrow\
\Gamma,\Delta[x:=u]\vdash J[x:=u].
\tag{Substitution}
\end{gathered}
\]

第二式には、WF 判断の対応する主張も含める。
より一般の weakening、すなわち well-formed な宣言を context の途中へ挿入する操作も許容的である。

**証明。**
weakening は判断の導出に関する同時帰納法。
provability の末尾への weakening は
\(\Proof P:P:*^p\)、weak type、provable の三規則でも得られる。
途中への挿入では、context の順序を保って全 premise に同じ宣言を挿入する。
局所変数は挿入する宣言の変数と異なる名前に取り直す。
variable の場合は宣言位置まで variable を使い、その後続を weak type で追加する。

代入は WF、sorting、typing、provability の導出の同時帰納法。
variable が \(x^s\) の場合は \(u\) の導出を代入後の後続 context へ weakening する。
他の変数は、その宣言を代入した context の variable と weakening で得る。
start では型の sorting に帰納法を使い、代入後の宣言を追加する。
axiom は context を持たず、代入で変化しない。
weak sort/type では代入対象の宣言を追加した step だけを削除し、他の step を再構成する。

conversion では、raw reduction が代入で保存されることを使う。
root beta は代入の合成則、その他の root は規則中の metavariable への同一の代入による。
繰り返し現れる型添字にも同じ代入を行うため、添字の一致は失われない。
compatible closure と有限 zigzag に拡張すれば
\(T\equiv_0T'\Rightarrow T[x:=u]\equiv_0T'[x:=u]\)。

dep form/intro/elim、subset form、prec、id elim、acc intro では、
局所 binder を fresh にして premise に帰納法を使う。
結論中の \(B[y:=a]\)、\(P[y:=r]\) には代入の合成則を使う。
残る規則は、表示された項への代入と規則の instance 化が可換である：
type elem/sort、provable/Proof、Power/Ty/Pred、subset intro/weak/prop、
id form/intro、exists、Take、RunStep の constructor、acc form/descent、run/runCase。
すべての premise は元の導出の真部分木であり、循環的な帰納法は使っていない。□

<a id="regularity"></a>

### Regularity と命題の conversion

\[
\begin{aligned}
\Gamma\vdash T:s\text{ または }\Gamma\vdash t:T:s\text{ または }\Gamma\vDash P
&\Longrightarrow\operatorname{WF}(\Gamma),\\
\Gamma\vdash t:T:s&\Longrightarrow\Gamma\vdash T:s,\\
\Gamma\vDash P&\Longrightarrow\Gamma\vdash P:*^p.
\end{aligned}
\tag{Regularity}
\]

**証明。** 導出の同時帰納法。
WF の主張は各規則の context premise を遡る。
typing の variable は start の sorting を weakening する。
conversion、dep intro、type elem、Take、continue/finish、run/runCase は
明示された formation premise、またはそれらからの Power/Ty/RunStep formation を使う。
dep elim と prec の結果型の sorting は Substitution。
Proof の場合は provability 側の帰納法である。

provable は typing 側の帰納法を使う。
subset prop、id intro、exists intro、acc intro/descent は対応する formation を適用する。
take equal は premise の Take typing と dep elim による \(f@t\) の typing に id form を適用する。
id elim では \(\Gamma,x:A\vdash P:*^p\) から type elem によって
\(P:*^p:\sq^p\) を得る。
\((*^s_i,\sq^p,\sq^p)\in\mathcal R\) により \(\lambda x:A.P\) を型付けし、
\(b\) に適用して type sort を使えば、結論の proposition の sorting を得る。
subset form の結果型は Power formation。
type sort は typing の premise 自身から WF を得る。
これで全規則の場合を尽くす。□

従って、次は許容的である。

\[
\Gamma\vDash P,\quad \Gamma\vdash Q:*^p,\quad P\equiv_0Q
\quad\Longrightarrow\quad\Gamma\vDash Q.
\tag{Prop-conversion}
\]

実際、Proof、conversion、provable をこの順に適用すればよい。
これは命題の構文的な conversion であって、集合モデルの意味保存ではない。

<a id="subject-reduction"></a>

## Subject reduction の到達点と未解決部分

<a id="principal-root"></a>

### 証明できる principal root の保存

以下では、消去規則の premise に現れる constructor の typing が、
対応する導入規則そのものによって与えられている場合を principal と呼ぶ。
型・motive の表示はその導入と消去で一致するとする。

- beta：lambda の body typing に Substitution を適用する。
- Pred/subset：subset の premise の \(P:*^p\) から
  \(\lambda x:A.P\) を [Regularity と命題の conversion](#regularity) と同じ方法で型付けし、a に適用する。
  type sort により結果の sorting は \(*^p\)。
- prec/continue と prec/finish：constructor の argument typing を取り出し、
  対応する branch に dep elim を適用する。motive の代入が結果型そのものである。
- run：\(f@a\) を dep elim で型付けする。
  id intro で \(\Gamma\vDash f@a=f@a\) を得れば、runCase の全 premise が揃う。
- runCase/continue：constructor の premise から \(a':A:*^s_i\)。
  Acc と equality の premise に acc descent を適用して Acc(f,a') を得る。
  run によって reduct の \(B:*^s_i\) での typing を得る。
- runCase/finish：constructor の premise がそのまま \(b:B:*^s_i\)。

これらは集合モデルを使わない導出の構成である。
しかし次の一般形を証明したことにはならない。

\[
\begin{aligned}
\Gamma\vdash t:T:s,\ t\Rightarrow_0t'
 &\Longrightarrow\Gamma\vdash t':T:s,\\
\Gamma\vdash T:s,\ T\Rightarrow_0T'
 &\Longrightarrow\Gamma\vdash T':s.
\end{aligned}
\tag{SR}
\]

sorting の SR があれば、provability の対応する主張は Prop-conversion から従う。

### 一般の SR に必要な議論

constructor の typing は最後が導入規則とは限らず、
conversion、subset intro/weak、weakening、type elem/sort を経由する。
特に \(t:A\) と \(t:\Ty(A,S)\) は同時に導出され得るので、
通常の PTS の「型の一意性」をそのまま引用してはいけない。

必要なのは少なくとも次である。

1. 上記の迂回を含む generation。lambda、subset、continue、finish の
   導出から、消去規則が要求する型での body/argument の導出を回収する。
2. binder の型注釈を簡約した場合の context conversion と、
   motive/body の型の変化を追う substitution。
3. subset intro の subject を簡約するとき、typing の保存と
   \(\Pred(A,S,t)\) の provability の移送を同時に扱う。
4. constructor の重複した型添字の一方だけを簡約した場合も含む compatible closure。

[補助 reduction の合流性](confluence.md#auxiliary-reduction) が示したのは、内外の添字の一致条件を外した
補助関係 \(\rightsquigarrow\) の合流性である。
\(\equiv_0\) の両端は補助関係で join するが、
共通簡約先の typing や元の関係 \(\Rightarrow_0\) の合流性はそこからは出ない。

証明上の別案として、conversion を \(\rightsquigarrow\) の同値閉包に広げた
体系 \(\mathcal S_+\) を定義できる。
元の有限導出はそのまま \(\mathcal S_+\) の導出になる。
この大きな体系の健全性を示せば元の無矛盾性は従う。
ただし、\(\mathcal S_+\) の generation、SR、意味保存は別途証明する必要があり、
その SR を元の体系の SR と呼んではならない。

TC の定義は[集合モデル](model.md#tc)、意味保存の未解決部分は[条件付き健全性](soundness.md#tc-obligation)を参照する。

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
