# Box 消去

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
well-termination の略記は、その二つの判断の導出へ展開して数える。
[Typing の基本補題](typing.md)を使い、Box-free 判断についての保守性を示す。

## Reflection の構文的性質

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

## 消去写像と導出の保存

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
Box の保守性を非自明な閉じた datatype payload に拡張するには [一般の datatype への拡張](proof.md#datatypes) が必要である。

Box-free 判断では消去は恒等なので、Clear はその範囲で保守性を与える。
