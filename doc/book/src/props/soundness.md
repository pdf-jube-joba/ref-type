# Core calculus の条件付き健全性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
以下では現行の構文 family と rule label を保持し、Set/Prop の判断を扱う。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
[集合モデル](model.md)の集合論的仮定・解釈・条件 [TC](model.md#tc) と、
[Typing の基本補題](typing.md)を使う。Trace、Prop-product、Run-laws、Semantic-substitution、Val は集合モデルの定義・補題を指す。

**定理（条件付き）。** [現行の TC](model.md#tc) が成り立つなら、任意の \(\rho\in\operatorname{Val}(\Gamma)\) について

\[
\begin{aligned}
\Gamma\vdash_0T:s&\Longrightarrow
 \llbracket T\rrbracket_\rho\in\llbracket s\rrbracket,\\
\Gamma\vdash_0e:T&\Longrightarrow
 \llbracket e\rrbracket_\rho\in\llbracket T\rrbracket_\rho,\\
\Gamma\vDash_0P&\Longrightarrow\llbracket P\rrbracket_\rho=1.
\end{aligned}
\tag{Soundness}
\]

## 帰納命題の強化

take equal の premise は Take の typing であり、定値性の証明そのものではない。
そこで項 typing の帰納命題に、subject が文字どおり
\(\Take^s_i(X,T,f)\) または \(\Take^p_i(X,T,g)\) である場合の次の性質を加える。
次の式の \(f\) は、その Take の関数引数を表す（prop の場合は \(g\)）。

\[
X_\rho\ne\varnothing,\qquad
\exists y.\ \forall x\in X_\rho.\
\operatorname{app}(f_\rho,x)=y.
\tag{K}
\]

K は syntax 中の任意の部分項についての主張ではない。
結論の subject が Take である導出についてだけ要求する。
この subject を直接作る規則は二つの take elim だけである。
weak、conversion、subset intro/weak は、
同じ subject を持つ真部分木へ遡れる。
他の規則の結論の subject は別の constructor である。
この有限の遡及により、K を通常の健全性と同時に証明できる。

## PTS と universe

**証明。** kind formation、型演算子 typing、項 typing、provability について、
Soundness と K を導出の高さで同時に帰納する。
各 premise は任意の valid valuation に対する帰納法の仮定を持つ。

axiom は \(U_i\in U_{i+1}\)、\(\mathbb B\in U_\omega\)。
variable は Val の定義、weakening は valuation の制限。
start では、context の新しい変数の値を表示型の要素から取る。
conversion は、現行規則に明示された元の型・目標型の二つの formation premise に TC を使う。
これで元の型の要素を目標型の要素として扱える。K の値は subject が同じなので変わらない。

dep form の universe 検査は、R の各 instance に対応して次のとおりである。

| domain sort | codomain sort | 結果が属する集合 |
| --- | --- | --- |
| \(*^s_i\) | \(*^s_j\) | \(U_{\max(i,j)}\) |
| \(*^s_i\) | \(\square^s_j\) | \(U_{\max(i,j)+1}\) |
| \(\square^s_i\) | \(\square^s_j\) | \(U_{\max(i,j)+1}\) |
| \(\square^s_i\) | \(*^s_j\) | \(U_{\max(i+1,j)}\) |
| \(*^p,\square^p,*^s_i,\square^s_i\) | \(*^p\) | \(\mathbb B\) |
| \(\square^p,*^s_i,\square^s_i\) | \(\square^p\) | \(U_\omega\) |

最初の四行では、domain と全 fiber が表示された universe に属する。
例えば第四行は \(A\in U_{i+1}\)、\(B(a)\in U_j\) なので
\(U_{\max(i+1,j)}\) 内で Trace 補題 4 を適用できる。
Prop の行は Prop-product であり、domain の大きさを \(\mathbb B\) 内に制限しない。
最後の行は \(U_i,U_{i+1}\in U_\omega\) と universe の推移性から
domain と全 fiber が \(U_\omega\) に属するため、Trace 補題 4 を使える。
これは対象体系に cumulativity を追加せず、外部集合の包含だけを使う。

dep intro は、各 \(a\in\llbracket A\rrbracket_\rho\) について
body の帰納法を \(\rho[x:=a]\) に適用する。
得た関数の trace は product の要素である。
dep elim は Trace 補題 2 と Semantic-substitution。
どちらにも proof/data の分岐や型の一意性は不要である。

## 論理・subset・Take

provable では、明示された formation premise の帰納法により
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

exists form は非空性の真理値なので \(\mathbb B\) の要素。
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

## RunStep・Acc・run

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
これで datatype を含まない現行 Box-free core の全規則と、強化した帰納命題を検証した。
この証明で TC を使ったのは conversion の場合だけである。□

<a id="conversion-free"></a>

## conversion を使わない導出についての無条件の結果

\(\mathcal S_0^{-}\) を、現行 Box-free core から conversion 規則だけを削除した体系とする。
これは補助的な部分体系であり、現行の conversion の定義を変更するものではない。
「conversion を使わない」とは、typing・provability・WF の全 premise の導出を含めて
その規則を使わないという意味である。raw reduction の定義自体は変えない。

**定理。** 外部の集合論的仮定だけのもとで、\(\mathcal S_0^{-}\) に対して Soundness が成り立つ。

**証明。** 上の導出帰納法から conversion の場合を取り除く。
残りの各場合で使ったのは、真部分木の帰納法、Val の定義、
Trace、Semantic-substitution、Run-laws と K だけである。
それらの定義・集合論的証明は TC を使わない。
provable の formation も現行規則の明示的な premise なので、
conversion を含む新しい Regularity の導出に帰納法を適用する必要はない。
よって同じ同時帰納法が外部の集合論だけで閉じる。□

**系。** \(\mathcal S_0^{-}\) は相対無矛盾である。
\[
\bot=\Pi_{(\square^p,*^p,*^p)}X_{*^p}:*^p.X_{*^p},
\qquad
\neg(\varnothing\vDash_0^-\bot),\qquad
\neg\exists t.\ \varnothing\vdash_0^-t:\bot.
\]
実際、\(\llbracket\bot\rrbracket=0\) なので、Soundness の provability と typing の
結論がそれぞれ \(0=1\)、\(\llbracket t\rrbracket\in\varnothing\) を要求して矛盾する。□

これは現行の全導出に対する無矛盾性ではない。
beta で等しい型の間を移る通常の導出も conversion を使うため、
この系だけでは現行体系の目標を満たさない。

## 所属条件のもとでの beta の意味保存

**補題。** 現行の rule label \(r=(\sigma_1,\sigma_2,\sigma_3)\) を固定する。
\(a_\rho=\llbracket a\rrbracket_\rho\in\llbracket A\rrbracket_\rho\) なら
\[
\llbracket(\lambda_r z:A.e)@_r a\rrbracket_\rho
=\llbracket e[z:=a]\rrbracket_\rho.
\tag{Beta-valid}
\]

**証明。** 左辺は
\(\operatorname{app}(\operatorname{lam}_{\llbracket A\rrbracket_\rho}
(v\mapsto\llbracket e\rrbracket_{\rho[z:=v]}),a_\rho)\)。
所属条件と Trace 補題 1 により
\(\llbracket e\rrbracket_{\rho[z:=a_\rho]}\) となる。
Semantic-substitution により右辺に等しい。□

特に、\(\mathcal S_0^{-}\) で型付けされた principal beta redex では、
argument premise に上の無条件 Soundness を適用して所属条件を得られる。
その root の意味保存には TC は不要である。
しかし任意の raw zigzag の中間項にこの argument premise があるとは限らない。

<a id="tc-obligation"></a>

## TC は raw 解釈の全域性からは従わない

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
現在、[補助体系での SR と型付きの共通簡約先](subject_reduction.md#typed-join)は得られている。
それに加えて、型の付いた reduction の意味保存を、
Soundness を TC で証明する帰納法と循環しない形で示す必要がある。
「Soundness で argument の所属を得て意味保存を示し、
その意味保存で TC を得て Soundness を示す」という順序は循環する。

ここに残る証明義務は TC そのものであり、
「通常の帰納法」や外部論文の typed equality の定理で代用してはいない。
Lee–Werner の体系は equality を型付きの判断として持つ。
現行体系の raw conversion との対応は、その論文の定理の仮定には含まれない
（[同論文 §2 の judgmental equality](https://arxiv.org/pdf/1111.0123)）。
