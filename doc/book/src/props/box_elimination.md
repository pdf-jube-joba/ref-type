# Box 消去

対象は [system.md](../system.md) の、宣言環境が空の体系である。
Box を含む Set/Prop の判断を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いたものを
\(\mathcal S_0\) と書く。Program の kind・型演算子・多相性は含める。
well-termination は定義中の二つの導出に展開する。

## Reflection と代入

名前の反映は単射で、Set の自由変数と衝突しないように取る。
Program の rule label の反映は現行の \(\bar r\) を使う。
\(\mathcal R_{pr}\) の各行を \(\mathcal R_s\) と照合すると
\(r\in\mathcal R_{pr}\Rightarrow\bar r\in\mathcal R_s\) である。
とくに型引数を取る積の結果レベルは \(\max(i+1,j)\) になる。

**補題（反映と代入）。** kind・型演算子・Program 項のいずれについても、
同じ構文 family の変数と代入項に対し
\[
\operatorname{Rf}(e[z:=a])
=_\alpha\operatorname{Rf}(e)[\bar z:=\operatorname{Rf}(a)].
\tag{Rf-subst}
\]

**証明。** 三構文の構造に関する同時帰納法。
変数は単射性、base kind は定義による。積・lambda・application は
rule label を固定して各引数に帰納法を適用する。
binder は自由変数を捕獲しない名前に取り直す。
F、U、return、thunk、force は反映で外側の記号を消すだけなので帰納法そのもの。
RunStep、continue、finish、run、runCase は引数ごとの帰納法。
sequence と value let は反映後の lambda の注釈・body・argument に帰納法を使う。
これで宣言環境が空の場合の全 constructor を尽くす。□

## Program の型・kind の反映

**補題（formation の反映）。**
\[
\begin{aligned}
\operatorname{WF}(\Theta)&\Longrightarrow
 \operatorname{WF}(\operatorname{RfCtx}(\Theta)),\\
\Theta\vdash K:\square^q_i&\Longrightarrow
 \operatorname{RfCtx}(\Theta)\vdash_0\operatorname{RfKind}(K):\square^s_i,\\
\Theta\vdash P:K&\Longrightarrow
 \operatorname{RfCtx}(\Theta)\vdash_0\operatorname{RfType}(P):\operatorname{RfKind}(K).
\end{aligned}
\tag{Rf-formation}
\]

ここで \(\Theta\) は Program の型変数だけの context である。
\(K=*^q_i\) とすれば、通常の Program 型の formation が得られる。

**証明。** まず Program type/kind の raw reduction の反映を確認する。
root は型演算子の beta であり、Rf-subst により Set の beta に写る。
compatible closure は対応する引数位置の closure に写る。
従って同じ family 内の有限 zigzag も反映先の conversion に写る。

次に WF・kind formation・型演算子 typing の有限導出について同時帰納する。
empty、axiom、start、variable、weak は反映先の同じ規則を使う。
conversion は両方の formation premise の帰納法と上の raw conversion の保存を使う。
dep form/intro/elim は \(\bar r\in\mathcal R_s\) と Rf-subst による。
F/U formation は premise の反映そのものであり、function、type product、
RunStep formation は反映先の対応する formation である。
Program の型・kind は Program 項を含まず、その自由変数も型変数に限られるため、
この帰納法に Program の run の typing は入らない。□

これは Program 項の typing の反映を意味しない。
Program の run は Acc を要求しないので、項の反映には well-termination の別の premise が必要である。

## Program reduction の simulation

**補題。**
\[
p\Rightarrow_{\mathsf{Tm}_{*^c_i}}p'
\Longrightarrow
\operatorname{RfTerm}(p)\Rightarrow_0^*\operatorname{RfTerm}(p').
\tag{Rf-step}
\]

**証明。** force/thunk は反映後に同じ項になる。
値 beta と型 beta は、それぞれ反映した rule label の Set beta と Rf-subst を使う。
return/sequence と value let も Set beta になる。
run は反映先の run root に写る。runCase/return-continue は反映先の
runCase/continue、runCase/return-finish は runCase/finish に写る。
Program evaluation context の各形は、反映後に Set の compatible context になる。
とくに sequence の評価位置は反映後の application の argument である。
導出に関する帰納法で閉包の場合を得る。□

## 消去写像

Set/Prop の通常の constructor と rule label には準同型に作用し、以下を追加する。
\[
\begin{aligned}
\lfloor\operatorname{Box}(P)\rfloor&=\operatorname{RfType}(P),\\
\lfloor\operatorname{box}_P(p)\rfloor&=\operatorname{RfTerm}(p),\\
\lfloor\operatorname{Force}_P(t)\rfloor&=\lfloor t\rfloor,\\
\lfloor\operatorname{bapp}_{A,\underline B}(f,a)\rfloor
 &=\lfloor f\rfloor @_{s^{i,j}}\lfloor a\rfloor,\\
\lfloor\operatorname{btapp}_{X:K,\underline B}(f,P)\rfloor
 &=\lfloor f\rfloor @_{\overline{r^{q;i,j}_{tc}}}\operatorname{RfType}(P).
\end{aligned}
\]
context 内の型・kind も消去する。
三構文の構造帰納法と Rf-subst によって、消去は構文 family と Set/Prop 代入を保存する。

**補題。**
\[
e\Rightarrow_\Box e'\Longrightarrow
 \lfloor e\rfloor\Rightarrow_0^*\lfloor e'\rfloor,\qquad
A\equiv_\Box B\Longrightarrow\lfloor A\rfloor\equiv_0\lfloor B\rfloor.
\tag{Clear-conversion}
\]

**証明。** 通常の Set/Prop root は同じ rule label の root に写る。
box step は Rf-step、force box は定義から反映後に同じ項になる。
bapp の両辺は反映した値 application に一致する。
btapp の両辺は反映した型 application に一致する。
後者の消去では、結果型に Rf-subst を使う。
compatible position が消去後も残ればそこで閉包を取り、
消去される注釈の位置なら両辺が同じになる。有限 zigzag の連結で後半を得る。
force box の停止性・typing の側条件を逆向きに証明する必要はない。□

## 導出の保存

**定理（Box 消去）。** Set/Prop の WF、kind formation、型演算子 typing、
項 typing、provability について
\[
\mathcal S_\Box\vdash J\Longrightarrow
\mathcal S_0\vdash\lfloor J\rfloor.
\tag{Clear}
\]

**証明。** well-termination を展開した有限導出について同時帰納する。
通常の規則は premise に帰納法を適用して同じ規則を再構成する。
conversion の側条件は Clear-conversion、代入を含む結論は消去と代入の可換性を使う。

- box type：空 context での Rf-formation を得て、消去した context へ weakening する。
- box intro：well-termination の Set typing の導出
  \(\varnothing\vdash_\Box\operatorname{RfTerm}(p):\operatorname{RfType}(P)\)
  は真部分木である。それに帰納法を適用し、消去した context へ weakening する。
- force box：帰納法で得た premise が、消去後の結論そのものである。
- bapp：明示された \(A,\underline B\) の formation premise に Rf-formation を使う。
  二つの項 typing premise の帰納法と、反映した formation に dep elim を適用する。
- btapp：Rf-formation により
  \[
  \varnothing\vdash_0\operatorname{RfKind}(K):\square^s_i,\qquad
  \bar X:\operatorname{RfKind}(K)\vdash_0\operatorname{RfType}(\underline B):*^s_j,\qquad
  \varnothing\vdash_0\operatorname{RfType}(P):\operatorname{RfKind}(K).
  \]
  これらを消去後の context へ weakening する。
  \(f\) の typing の帰納法に dep elim を適用すると、結果型は
  \(\operatorname{RfType}(\underline B)[\bar X:=\operatorname{RfType}(P)]\)。
  Rf-subst により \(\operatorname{RfType}(\underline B[X:=P])\) と一致する。

以上の帰納法で、Set typing を含む well-termination を結論側から仮定してはいない。□

Box-free 判断では消去は恒等なので、Clear はその範囲で保守性を与える。
[無矛盾性](proof.md)には、この定理に加えて Box-free core の健全性が必要である。

## 閉じた多相 Program 型

現行 core では、datatype がなくても閉じた Program 型を形成できる。
例えば \(r_0=r^{0,0}_{vc}\)、\(r_1=r^{v;0,0}_{tc}\) と置くと
\[
P=\Pi_{r_1}X_{*^v_0}:*^v_0.\,
       (X_{*^v_0}\to_{r_0}F X_{*^v_0})
\]
に対し \(\varnothing\vdash P:*^c_1\) である。
実際、\(X:*^v_0\) の context で variable、F form、function form を使い、
最後に type product を適用すればよい。
従って Box 消去を「閉じた Box を形成できないから自明」とは証明できない。
datatype を含める場合には、さらに[宣言・case の反映](proof.md#datatypes)が必要になる。
