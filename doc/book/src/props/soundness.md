# Core calculus の条件付き健全性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
[集合モデル](model.md)の集合論的仮定・解釈・条件 [TC](model.md#tc) と、
[Typing の基本補題](typing.md)を使う。Trace、Prop-product、Run-laws、Semantic-substitution、Val は集合モデルの定義・補題を指す。

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

## 帰納命題の強化

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

## PTS と universe

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

## 論理・subset・Take

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
これですべての Box-free core の規則と、強化した帰納命題を検証した。□

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
それに加えて、型の付いた reduction の意味保存を、
Soundness を TC で証明する帰納法と循環しない形で示す必要がある。
「Soundness で argument の所属を得て意味保存を示し、
その意味保存で TC を得て Soundness を示す」という順序は循環する。

ここに残る証明義務は TC そのものであり、
「通常の帰納法」や外部論文の typed equality の定理で代用してはいない。
Lee–Werner の体系は equality を型付きの判断として持つ。
現行体系の raw conversion との対応は、その論文の定理の仮定には含まれない
（[同論文 §2 の judgmental equality](https://arxiv.org/pdf/1111.0123)）。
