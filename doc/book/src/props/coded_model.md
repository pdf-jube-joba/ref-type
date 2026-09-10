# 型コードによる集合モデル

対象は datatype と Box を除いた Set/Prop core である。
[従来の候補解釈](model.md)とは別のモデルを構成する。
型をその要素集合と同一視せず、型コードとその decoding を区別する。
証明項は消去するが、命題、型演算子、kind は消去しない。
この区別を使う[conversion の証明](semantic_conversion.md)は、従来の TC を仮定しない。

## 型コードの構成

集合論的仮定、\(0,1,\mathbb B\)、trace の app/lam/Prod は
[集合モデル](model.md#universes)のものを使う。
以下の constructor は、相異なる有限 ordinal の tag と通常の ordered tuple で符号化する。
従って constructor と引数について単射であり、異なる tag の像は交わらない。
コードの集合としての rank は、格納した各引数の rank より大きい。

valid なコード c とその decoding \(\operatorname{El}(c)\) を、
集合の rank に関する再帰で同時に定める。
表の条件に合わない集合は invalid とし、その El を空集合とする。

| コード | valid である条件 | El |
| --- | --- | --- |
| \(\mathsf u_i:=\langle\mathrm{univ},U_i\rangle\) | \(i\in\mathbb N\) | \(\mathcal C_i:=\{c\in U_i\mid c\text{ は valid}\}\) |
| \(\mathsf p\) | 常に | \(\mathbb B\) |
| \(\mathsf q(P)\) | \(P\in\mathbb B\) | P |
| \(\mathsf{pi}_r(c,F)\) | c は valid、F は domain El(c) の通常の集合論的関数、各 F(a) は valid | \(\operatorname{Prod}(\operatorname{El}(c),a\mapsto\operatorname{El}(F(a)))\) |
| \(\mathsf{pow}(c)\) | c は valid | \(\mathcal P(\operatorname{El}(c))\) |
| \(\mathsf{ref}(c,S)\) | c は valid、\(S\subseteq\operatorname{El}(c)\) | S |
| \(\mathsf{sum}(c,d)\) | c、d は valid | \((\{0\}\times\operatorname{El}(c))\cup(\{1\}\times\operatorname{El}(d))\) |

pi の F は trace でなく通常の関数の graph として格納する。
domain が空でも、pi コード自体には domain コード c が残る。
\(\mathsf p\)、\(\mathsf q\) にもそれぞれ別の tag を使う。

**再帰が正当であること。** 通常の constructor では、参照するコード c、d、F(a) は
いずれもコード全体より rank が小さい。
univ の場合も、\(d\in U_i\) の rank は \(\mathsf u_i\) の rank より小さい。
従って \(\mathcal C_i\) の定義は、\(\mathsf u_i\) 自身の validity を参照しない。
特に、\(\mathsf u_i\notin U_i\) である。
\(\mathsf u_i\) を単に自然数 i で表すとこの根拠を失うため、U_i 自体をコードに格納した。
集合の well-founded recursion と Separation によって El と各 \(\mathcal C_i\) が定まる。
ここでの class 関数は ZFC における定義可能 class の略記である。

\(\mathcal C_\omega:=\{c\in U_\omega\mid c\text{ は valid}\}\) とも置く。
\(\mathsf u_\omega\) というコードは追加しない。

**小ささの補題。** \(U\in\{U_i\mid i\in\mathbb N\}\cup\{U_\omega\}\) について
\[
c\in U,\quad c\text{ は valid}\quad\Longrightarrow\quad\operatorname{El}(c)\in U.
\tag{Code-smallness}
\]

**証明。** c の rank で帰納する。
univ では \(\mathsf u_j\in U\) から推移性により \(U_j\in U\)。
\(\mathcal C_j\subseteq U_j\) と powerset に関する閉性により \(\mathcal C_j\in U\)。
pi では El(c) と各 El(F(a)) が U に属するので、universe の indexed family に関する閉性と
Trace の積の補題を使う。pow、ref、sum は powerset、subset、pair、union の閉性。
残りは有限集合である。□

逆に、valid な引数コードが U に属し、pi の domain の decoding が U に属し、
各 fiber コードが U に属すれば、作ったコードも U に属す。
pi の F を U 内で作れることは indexed family に関する閉性による。
ref では \(S\subseteq\operatorname{El}(c)\) と Code-smallness を使う。

## 証明項の消去

\(\epsilon(e)\) は、family \(\mathsf{Tm}_{*^p}\) の式全体を定数 \(\bullet\) に置き換え、
他の family では全引数・注釈・binder body に再帰する写像とする。
例えば、証明を返す lambda/application/Take/prec は全体が消えるが、
命題を返す型演算子の lambda/application と、命題の product は残る。
context の宣言は残し、宣言型だけを消去する。proof variable の出現も \(\bullet\) になる。

この写像は構文 family だけで決まり、typing 導出を調べない。
消去後の式には proof variable の自由な出現がない。
捕獲を避けた代入について
\[
\epsilon(e[z:=a])=\epsilon(e)[z:=\epsilon(a)].
\tag{Erase-substitution}
\]
proof variable z の場合は両辺とも \(\epsilon(e)\)。他の場合は構文帰納法である。

## 消去構文の全域的解釈

以下の \(\langle e\rangle_\rho\) は消去後の raw 構文の解釈である。
\(\langle\bullet\rangle_\rho=0\)、残る変数は \(\rho\) で解釈する。
base kind は \(\langle *^s_i\rangle=\mathsf u_i\)、\(\langle *^p\rangle=\mathsf p\)。

domain の sort を保持するため、次の略記を使う。
\[
\delta_\sigma(v):=
\begin{cases}\mathsf q(v)&\sigma=*^p,\\v&\text{otherwise},\end{cases}
\qquad
|A|_{\sigma,\rho}:=\operatorname{El}(\delta_\sigma(\langle A\rangle_\rho)).
\]
命題 P が形成されている場合は \(|P|_{*^p,\rho}=\langle P\rangle_\rho\)。

\(r=(\sigma_1,\sigma_2,\sigma_3)\) とし、\(D=|A|_{\sigma_1,\rho}\)、
\(F(a)=\langle B\rangle_{\rho[z:=a]}\) と置く。
\[
\langle\Pi_r z:A.B\rangle_\rho=
\begin{cases}
\mathbf t(\forall a\in D.\ F(a)=1)&\sigma_2=*^p,\\
\mathsf{pi}_r(\delta_{\sigma_1}(\langle A\rangle_\rho),F)&\sigma_2\ne *^p.
\end{cases}
\tag{Coded-product}
\]
ここで F は domain D の通常の graph であり、\(\mathbf t\) は真なら 1、偽なら 0。
第二行の constructor は invalid な引数についても tuple 自体を返す。
型付けされた場合に valid であることは後で証明する。

残っている lambda と application は
\[
\langle\lambda_r z:A.m\rangle_\rho
=\operatorname{lam}_{|A|_{\sigma_1,\rho}}
 (a\mapsto\langle m\rangle_{\rho[z:=a]}),\qquad
\langle f@_r a\rangle_\rho=\operatorname{app}(\langle f\rangle_\rho,\langle a\rangle_\rho).
\]
その結果 family は proof ではない。proof を返すものは既に \(\bullet\) である。

以下では c、d、S、a、f などは対応する構文引数の解釈を表す。

| 構文 | 解釈 |
| --- | --- |
| \(\Power A\) | \(\mathsf{pow}(c)\) |
| \(\Ty(A,S)\) | \(\mathsf{ref}(c,S)\) |
| \(\{x:A\mid P\}\) | \(\{a\in\operatorname{El}(c)\mid\langle P\rangle_{\rho[x:=a]}=1\}\) |
| \(\Pred(A,S,a)\) | \(\mathbf t(a\in S)\) |
| \(a=b\) | \(\mathbf t(a=b)\) |
| \(\exists A\) | \(\mathbf t(\operatorname{El}(c)\ne\varnothing)\) |
| \(\Take^s_i(X,T,f)\) | \(\bigcup\{\operatorname{app}(f,x)\mid x\in\operatorname{El}(\langle X\rangle_\rho)\}\) |
| \(\operatorname{RunStep}(A,B)\) | \(\mathsf{sum}(c,d)\) |
| \(\operatorname{continue}_{A,B}(a)\), \(\operatorname{finish}_{A,B}(b)\) | \((0,a)\), \((1,b)\) |
| \(\operatorname{Acc}_{A,B}(f,a)\) | \(\mathbf t(a\in D_{\operatorname{El}(c),\operatorname{El}(d),f})\) |
| \(\operatorname{run}_{A,B}(f,a)\) | \(\operatorname{Run}_{\operatorname{El}(c),\operatorname{El}(d)}(f,a)\) |
| \(\operatorname{runCase}_{A,B}(f,a,r)\) | \(\operatorname{Case}_{\operatorname{El}(c),\operatorname{El}(d)}(f,r)\) |

残る prec は r が \((0,a)\) なら app(c,a)、\((1,b)\) なら app(d,b)、他は 0。
停止集合 D、Run、Case は[有限 accessibility の構成](model.md#termination)をそのまま使う。

すべての演算が任意の集合引数について定義されるため、raw 解釈は構文再帰で全域的に存在する。
構文帰納法により
\[
\langle e[z:=a]\rangle_\rho
=\langle e\rangle_{\rho[z:=\langle a\rangle_\rho]}.
\tag{Coded-substitution}
\]
proof variable の場合は、消去構文にその変数が出現しないことを使う。
これは raw reduction の意味保存を主張する補題ではない。

## Valuation と judgment の意味

\(\operatorname{Val}_c(\varnothing)=\{\varnothing\}\) とし、
\[
\operatorname{Val}_c(\Gamma,z^\sigma:A)
=\{\rho[z:=a]\mid\rho\in\operatorname{Val}_c(\Gamma),\ a\in|A|_{\sigma,\rho}\}.
\]
\(\Gamma\vdash e:T\)、\(e\in\mathsf E_\sigma\) の意味は、各 valid valuation で
\(\langle e\rangle_\rho\in|T|_{\sigma,\rho}\) である。
kind formation \(K:\square^s_i\)、\(K:\square^p\) の意味はそれぞれ
\(\langle K\rangle_\rho\in\mathcal C_{i+1}\)、\(\langle K\rangle_\rho\in\mathcal C_\omega\)。
provability の意味は \(\langle P\rangle_\rho=1\)。

dep form の閉性は次の表で尽くされる。

| domain sort | codomain sort | product の値が属する集合 |
| --- | --- | --- |
| \(*^s_i\) | \(*^s_j\) | \(\mathcal C_{\max(i,j)}\) |
| \(*^s_i\) | \(\square^s_j\) | \(\mathcal C_{\max(i,j)+1}\) |
| \(\square^s_i\) | \(\square^s_j\) | \(\mathcal C_{\max(i,j)+1}\) |
| \(\square^s_i\) | \(*^s_j\) | \(\mathcal C_{\max(i+1,j)}\) |
| \(*^p,\square^p,*^s_i,\square^s_i\) | \(*^p\) | \(\mathbb B\) |
| \(\square^p,*^s_i,\square^s_i\) | \(\square^p\) | \(\mathcal C_\omega\) |

例えば第四行では domain コードとその decoding が \(U_{i+1}\) に属し、
各 fiber コードは \(U_j\) に属するので、pi コードは \(U_{\max(i+1,j)}\) に属する。
他のコードの行も Code-smallness と indexed family の閉性による。
命題の product はコードを作らず真理値を返すため、impredicativity によるサイズの増加はない。

## このモデルが保持する情報

\(\mathsf{pi}_r(c,F)=\mathsf{pi}_{r'}(d,G)\) なら
\(r=r'\)、\(c=d\)、\(F=G\)。pow、ref、sum にも同じ injectivity がある。
これは decoding の集合が等しいという主張より強い。
例えば空集合を decoding に持つ二つの異なる関数型コードも区別する。

命題の product には、この injectivity を主張しない。
そのために proof を返す lambda/application を先に消去した。
消去後に残る beta redex の function type は、必ず pi コードで解釈される。
この点を[次の証明](semantic_conversion.md)の generation と意味保存に使う。

空の domain に対しても、\(\mathsf{pi}_r(c,\varnothing)\) の c は回収できる。
一方、\(\operatorname{El}(\mathsf{pi}_r(c,\varnothing))=1\) だけから c を回収することはできない。
また、\(\mathsf{ref}(c,S)\) と c は別のコードであり、refinement の導入・除去は
それぞれの typing 規則で扱う。コードの等号を subset の包含で置き換えてはいけない。
