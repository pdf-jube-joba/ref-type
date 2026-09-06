# Core calculus の相対無矛盾性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
well-termination の略記は、その二つの判断の導出へ展開して数える。

> **証明の到達点。**
> Box 消去、構文的代入、集合演算の構成、および下記の条件付き健全性を示す。
> raw conversion の意味保存 \(\mathrm{TC}\) は未証明である。
> したがって、現行体系の無条件の相対無矛盾性証明はまだ完成していない。
> subject reduction の一般形も、後述の principal root の場合と区別する。

## 1. 証明すべき命題

\[
\bot:=\Pi P^{\sq^p}:*^p.P.
\]

\((*^p,\sq^p)\in\mathcal A\)、
\((\sq^p,*^p,*^p)\in\mathcal R\) より \(\emptyset\vdash_0\bot:*^p\)。
目標は、外部の集合論 \(\mathsf{ZFC}\) と §4 の universe 仮定のもとで

\[
\neg(\emptyset\vDash_\Box\bot),\qquad
\neg\exists t.\ \emptyset\vdash_\Box t:\bot:*^p
\tag{Consistency}
\]

を示すことである。これは強正規化、Program の停止性、型検査の決定可能性とは別の命題である。

以下の証明は

\[
\text{Box 消去}\quad+\quad
\bigl(\mathrm{TC}\Longrightarrow\mathcal S_0\text{ の健全性}\bigr)
\quad+\quad\llbracket\bot\rrbracket=\varnothing
\]

までを与える。\(\mathrm{TC}\) を外部集合論の公理に紛れ込ませない。

## 2. 導出についての基本補題

ここでは \(\mathcal S_0\) を扱う。代入は context の後続の宣言にも作用する。
raw 代入の合成則は [構文的補題 §1](metatheory.md) を使う。

### 2.1 Weakening と substitution

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

### 2.2 Regularity と命題の conversion

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

## 3. Box 消去

### 3.1 Reflection の構文的性質

一般の datatype を除く Program syntax 上で RfType/RfTerm は全域的である。
Program 変数は Set 変数と衝突しない名前へ単射で写す。以下は構造帰納法による。

\[
\begin{aligned}
\operatorname{RfType}(P[X:=A])
&=_\alpha\operatorname{RfType}(P)[X:=\operatorname{RfType}(A)],\\
\operatorname{RfTerm}(p[x^v:=V])
&=_\alpha\operatorname{RfTerm}(p)[x^{*^s_0}:=\operatorname{RfTerm}(V)].
\end{aligned}
\tag{Rf-subst}
\]

Program type formation と context formation の同時帰納法から

\[
\Delta\vdash P\ \mathsf{ptype}
\ \Longrightarrow\
\operatorname{RfCtx}(\Delta)\vdash_0\operatorname{RfType}(P):*^s_0.
\tag{Rf-formation}
\]

変数の場合は reflected context の variable と type sort、
F/U は帰納法そのもの、関数型は
\((*^s_0,*^s_0,*^s_0)\in\mathcal R\)、RunStep はその formation による。
context の value 宣言はこの sorting を使って start で追加する。

\[
p\Rightarrow_cp'
\ \Longrightarrow\
\operatorname{RfTerm}(p)\Rightarrow_0^*\operatorname{RfTerm}(p').
\tag{Rf-step}
\]

**証明。** force/thunk は両辺の reflection が同じなので 0 step。
beta、sequence、let は Set beta と Rf-subst。
run と二つの runCase は対応する Set root。
Program evaluation context は、reflection 後には Set の compatible context になる。□

Program typing から reflected term の typing が従うとは主張しない。
Program run の規則には Acc premise がなく、Rf-step は raw 項についての主張である。

### 3.2 消去写像と導出の保存

通常の Set constructor には準同型に作用させ、以下を追加する。

\[
\begin{aligned}
\lfloor\operatorname{Box}(P)\rfloor&=\operatorname{RfType}(P),\\
\lfloor\operatorname{box}_P(p)\rfloor&=\operatorname{RfTerm}(p),\\
\lfloor\operatorname{Force}_P(t)\rfloor&=\lfloor t\rfloor,\\
\lfloor f@^{\operatorname{Box}}a\rfloor&=\lfloor f\rfloor @\lfloor a\rfloor.
\end{aligned}
\]

context の型も消去する。構造帰納法で消去と代入の可換性を得る。
さらに

\[
t\Rightarrow_\Box t'
\Longrightarrow\lfloor t\rfloor\Rightarrow_0^*\lfloor t'\rfloor,\qquad
t\equiv_\Box t'\Longrightarrow\lfloor t\rfloor\equiv_0\lfloor t'\rfloor.
\tag{Clear-conversion}
\]

Box-free root は同じ root に写る。
box step は Rf-step、force-box と boxed application は 0 step に写る。
context closure と zigzag への拡張に typing は不要である。

**定理（Box 消去）。** 四判断について
\[
\mathcal S_\Box\vdash J\Longrightarrow\mathcal S_0\vdash\lfloor J\rfloor.
\tag{Clear}
\]

**証明。** well-termination を展開した有限導出の同時帰納法。
通常の規則は同じ規則を適用する。conversion は Clear-conversion を使う。

box type は Rf-formation と weakening。
box intro の well-termination premise には
\(\emptyset\vdash_\Box\operatorname{RfTerm}(p):\operatorname{RfType}(P):*^s_0\)
の導出が含まれる。この真部分木に帰納法を適用してから weakening する。
この premise を最初から \(\mathcal S_0\) の導出だとは仮定しない。

force box の消去後の結論は帰納法で得た premise そのものである。
boxed application は、二つの premise の帰納法と通常の dep elim を使う。
その追加の formation premise は、premise の Regularity、Box formation の
由来にある Program type formation、および Rf-formation から得られる。
Box formation の由来は sorting/typing の導出を遡って調べる：
Box の sorting を直接作る規則は box type だけであり、type sort/elem、
weakening、conversion、subset の迂回からは新しい Program 型は作れない。
同じことを形式的に追うには、帰納命題に
「typing の表示型が \(\operatorname{Box}(P)\) なら \(\emptyset\vdash P\ \mathsf{ptype}\)」
を加える必要はない。消去後の premise に Regularity を適用すれば
\(\operatorname{RfType}(A)\)、\(\operatorname{RfType}(A)\to\operatorname{RfType}(\underline B)\)
の sorting が既に得られる。codomain の formation には、反映された
Program 型の構文に関する帰納法を使う。
□

最後の boxed application の formation を独立に確実にするため、次の事実も使える：
この core の空 Program context で形成できる Program 型は存在しない。
value type の葉は必ず自由な型変数であり、F/U、関数型、RunStep はそれを束縛しない。
したがって閉じた Box の導入・形成はこの core では使えない。
Box の保守性を非自明な閉じた datatype payload に拡張するには §9 が必要である。

Box-free 判断では消去は恒等なので、Clear はその範囲で保守性を与える。

## 4. 集合論的演算

### 4.1 Universe と trace encoding

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

### 4.2 決定的な停止計算

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

## 5. raw 項の解釈

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

D は §4.2 の \((A,B,f)\) に対応する集合。
prec の解釈は、r が \((0,a)\) なら \(\operatorname{app}(c,a)\)、
\((1,b)\) なら \(\operatorname{app}(d,b)\)、それ以外なら 0 とする。
motive と型添字は、この場合分けの値には使わない。

これらは項の構造再帰で定義される。
binder の body の評価は、異なる valuation のもとでも真部分項の評価である。
各段の indexed family は置換公理で集合になる。
Run は object term を再帰的に評価する演算ではなく、既に解釈した集合上の §4.2 の演算である。
従って、自由変数に値を与えたすべての raw 項の解釈が存在する。
型の付かない項については、簡約による値の保存を主張しない。

### 5.1 意味的代入

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

### 5.2 Context と未証明の conversion 条件

\[
\begin{aligned}
\operatorname{Val}(\emptyset)&=\{\emptyset\},\\
\operatorname{Val}(\Gamma,x^s:A:s)
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

TC の判断は現行体系の判断であり、結論の解釈は §5 の固定した写像である。
TC 自体を帰納的な規則として体系に追加してはいない。

## 6. 条件付き健全性

**定理。** TC が成り立つなら、任意の \(\rho\in\operatorname{Val}(\Gamma)\) について

\[
\begin{aligned}
\Gamma\vdash_0T:s&\Longrightarrow
 \llbracket T\rrbracket_\rho\in\llbracket s\rrbracket,\\
\Gamma\vdash_0t:T:s&\Longrightarrow
 \llbracket t\rrbracket_\rho\in\llbracket T\rrbracket_\rho,\\
\Gamma\vDash_0P&\Longrightarrow\llbracket P\rrbracket_\rho=1.
\end{aligned}
\tag{Soundness}
\]

### 6.1 帰納命題の強化

take equal の premise は Take の typing であり、定値性の証明そのものではない。
そこで sorting と typing の帰納命題に、subject が文字どおり
\(\Take(X,T,f)\) である場合の次の性質を加える。

\[
X_\rho\ne\varnothing,\qquad
\exists y.\ \forall x\in X_\rho.\
\operatorname{app}(f_\rho,x)=y.
\tag{K}
\]

K は syntax 中の任意の部分項についての主張ではない。
結論の subject が Take である導出についてだけ要求する。
この subject を直接作る規則は二つの take elim だけである。
weakening、conversion、subset intro/weak、type elem/sort は、
同じ subject を持つ真部分木へ遡れる。
他の規則の結論の subject は別の constructor である。
この有限の遡及により、K を通常の健全性と同時に証明できる。

### 6.2 PTS と universe

**証明。** 三判断について Soundness と K を導出の高さで同時に帰納する。
各 premise は任意の valid valuation に対する帰納法の仮定を持つ。

axiom は \(U_i\in U_{i+1}\)、\(\mathbb B\in U_\omega\)。
variable は Val の定義、weakening は valuation の制限。
type elem/sort は同じ集合所属を別の判断で記述したものである。
conversion は Regularity で得る元の型の sorting と、目標型の sorting に TC を使う。
これで元の型の要素を目標型の要素として扱える。K の値は subject が同じなので変わらない。

dep form の universe 検査は、R の各 instance に対応して次のとおりである。

| domain sort | codomain sort | 結果が属する集合 |
| --- | --- | --- |
| \(*^s_i\) | \(*^s_i\) | \(U_i\) |
| \(*^s_i\) | \(\sq^s_i\) | \(U_{i+1}\) |
| \(\sq^s_i\) | \(\sq^s_i\) | \(U_{i+1}\) |
| \(\sq^s_i\) | \(*^s_i\) | \(U_{i+1}\) |
| \(*^p,\sq^p,*^s_i,\sq^s_i\)（R で許されるもの） | \(*^p\) | \(\mathbb B\) |
| \(\sq^p,*^s_i,\sq^s_i\) | \(\sq^p\) | \(U_\omega\) |

最初の四行と最後の行は Trace 補題 4。
\(*^s_i\) の fiber は \(U_i\subseteq U_{i+1}\) でもある。
Prop の行は Prop-product であり、domain の大きさを \(\mathbb B\) 内に制限しない。
これは対象体系に cumulativity を追加する議論ではなく、外部集合の包含を使った閉性の確認である。

dep intro は、各 \(a\in\llbracket A\rrbracket_\rho\) について
body の帰納法を \(\rho[x:=a]\) に適用する。
得た関数の trace は product の要素である。
dep elim は Trace 補題 2 と Semantic-substitution。
どちらにも proof/data の分岐や型の一意性は不要である。

### 6.3 論理・subset・Take

provable では Regularity と既に得た sorting 健全性により
\(\llbracket P\rrbracket_\rho\in\mathbb B\)。
typing premise の値がこの集合の要素なので空集合ではなく、従って 1。
Proof は provability の帰納法による \(0\in1\)。

Power、Ty、subset form は powerset、subset、separation の universe 閉性。
Pred は定義から \(\mathbb B\) の要素。
subset intro は \(a\in A\) と \(\mathbf t(a\in S)=1\) から \(a\in S\)。
subset weak は \(S\subseteq A\) と \(a\in S\)。
subset prop は \(a\in S\) を真理値に戻す。
同じ subject の値を変えないので、subset の迂回も K を保存する。

id form/intro は集合の等号。
id elim では premise から \(a_\rho=b_\rho\)。
両方とも \(A_\rho\) の要素なので、Trace 補題 1 により
二つの predicate application はそれぞれ
\(\llbracket P\rrbracket_{\rho[x:=a_\rho]}\) と
\(\llbracket P\rrbracket_{\rho[x:=b_\rho]}\) に等しい。
valuation が等しいので真理値が一致する。

exists intro は表示された要素による非空性。
take elim set では二重の Prop-product により
\[
\forall x_1,x_2\in X_\rho.\
\operatorname{app}(f_\rho,x_1)=\operatorname{app}(f_\rho,x_2).
\]
非空性から一つ \(x_0\in X_\rho\) を取り、
\(y=\operatorname{app}(f_\rho,x_0)\in T_\rho\) とする。
像は \(\{y\}\) なので Take の値は \(\bigcup\{y\}=y\)。
同時に K が得られる。これは大域的な選択関数を解釈に加えることではない。

take elim prop では、X が非空で \(f_\rho\) が
\(\operatorname{Prod}(X_\rho,x\mapsto T_\rho)\) の要素である。
Prop-product により \(T_\rho=1\)、\(f_\rho=0\)。
各 app 値も 0、Take の値も 0 であり、所属と K の両方を得る。

take equal では typing premise の**強化した**帰納法により K を得る。
\(t_\rho\in X_\rho\) より、その一定値 y は
\(\operatorname{app}(f_\rho,t_\rho)\)。
非空性を使うと Take の値は y であり、結論の等号は真である。
単に「Take が T の要素だから f は定値」と推論してはいない。

### 6.4 RunStep・Acc・run

RunStep formation と constructor は universe 内の tagged sum。
prec では r の帰納法から \(r_\rho=(0,a)\) または \((1,b)\)。
前者なら \(a\in A_\rho\) であり、c の帰納法と Trace 補題 2 から
選んだ値が \(\llbracket P\rrbracket_{\rho[x:=(0,a)]}\) に属する。
後者も d と B について同じである。
Semantic-substitution で結論の表示型に一致する。
P が命題の場合にも同じ所属の議論が使える。

acc form は真理値の定義。
acc intro では、各 \(b\in A_\rho\) に対して拡張 valuation に帰納法を使う。
implication の Prop-product により
\(\operatorname{app}(f_\rho,a_\rho)=(0,b)\Rightarrow b\in D\)。
Run-laws の第一式から \(a_\rho\in D\)。
acc descent は同じ式の逆方向と equality premise。
run は Run-laws の第二式。

runCase では \(a_\rho\in D\)、\(r_\rho=\operatorname{app}(f_\rho,a_\rho)\)。
finish の場合は結果が直接 B の要素。
continue の場合は後続が D に属し、その Run の結果が B の要素である。
K を新たに要求する subject はここにはない。
これですべての Box-free core の規則と、強化した帰納命題を検証した。□

## 7. Subject reduction と TC の未解決部分

### 7.1 証明できる principal root の保存

以下では、消去規則の premise に現れる constructor の typing が、
対応する導入規則そのものによって与えられている場合を principal と呼ぶ。
型・motive の表示はその導入と消去で一致するとする。

- beta：lambda の body typing に Substitution を適用する。
- Pred/subset：subset の premise の \(P:*^p\) から
  \(\lambda x:A.P\) を §2.2 と同じ方法で型付けし、a に適用する。
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

### 7.2 一般の SR に必要な議論

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

[構文的補題 §2](metatheory.md) が示したのは、内外の添字の一致条件を外した
補助関係 \(\rightsquigarrow\) の合流性である。
\(\equiv_0\) の両端は補助関係で join するが、
共通簡約先の typing や元の関係 \(\Rightarrow_0\) の合流性はそこからは出ない。

証明上の別案として、conversion を \(\rightsquigarrow\) の同値閉包に広げた
体系 \(\mathcal S_+\) を定義できる。
元の有限導出はそのまま \(\mathcal S_+\) の導出になる。
この大きな体系の健全性を示せば元の無矛盾性は従う。
ただし、\(\mathcal S_+\) の generation、SR、意味保存は別途証明する必要があり、
その SR を元の体系の SR と呼んではならない。

### 7.3 TC は raw 解釈の全域性からは従わない

例えば raw beta について、a が解釈した domain に属する場合だけ
Trace 補題 1 と Semantic-substitution が beta の意味保存を与える。
domain の外では app の値は 0 であり、body の代入後の値と一致するとは限らない。
具体的には、\(\llbracket A\rrbracket_\rho=\varnothing\)、
\(\llbracket a\rrbracket_\rho=1\) とすると
\[
\llbracket(\lambda x:A.x)@a\rrbracket_\rho=0
\ne1=\llbracket a\rrbracket_\rho.
\]
これは型の付かない raw 項の例であり、TC の反例ではない。

従って、raw zigzag の各 step に無条件で解釈を適用する証明は使えない。
一方、SR と合流性だけでも十分ではない。
それに加えて、型の付いた reduction の意味保存を、
Soundness を TC で証明する帰納法と循環しない形で示す必要がある。
「Soundness で argument の所属を得て意味保存を示し、
その意味保存で TC を得て Soundness を示す」という順序は循環する。

ここに残る証明義務は TC そのものであり、
「通常の帰納法」や外部論文の typed equality の定理で代用してはいない。
Lee–Werner の体系は equality を型付きの判断として持つ。
現行体系の raw conversion との対応は、その論文の定理の仮定には含まれない
（[同論文 §2 の judgmental equality](https://arxiv.org/pdf/1111.0123)）。

## 8. 条件付きの無矛盾性

**定理。** §4 の集合論的仮定と TC のもとで Consistency が成り立つ。

**証明。**
\[
\llbracket\bot\rrbracket
=\operatorname{Prod}(\mathbb B,P\mapsto P)=0.
\]
実際、\(0\in\mathbb B\) に対応する fiber が空である。
もし \(\emptyset\vDash_0\bot\) なら Soundness により同じ値が 1 となって矛盾。
もし \(\emptyset\vdash_0t:\bot:*^p\) なら Soundness により
\(\llbracket t\rrbracket\in\varnothing\) となって矛盾。
Box 付きの導出は Clear により Box-free の導出へ移る。□

これは TC を証明したという主張ではなく、TC 以外のモデル側の接続を示す定理である。
現時点で得た結果は「この候補解釈に対する TC が成り立てば無矛盾」であり、
「現行体系の無矛盾性を証明した」ではない。

## 9. 一般の datatype を含める場合

ここまでの定理は、datatype の宣言・constructor も含めて除いた core の定理である。
Set case だけを除けば十分、とはしていない。
拡張には以下が必要になる。

1. declaration environment と strict positivity の形式的な定義。
2. reflection 後の signature の positivity と universe 内の最小不動点の構成。
3. Program case を含む reflection の全域的な定義と対応する Set case の規則。
4. case の代入・簡約 simulation と Box 消去の追加 case。
5. 追加規則についての健全性、および拡張した raw conversion の TC。

また、well-termination の定義に Set typing が含まれることと、
Program の operational な停止性を示すことは別である。
後者の定理はここでは主張しない。
