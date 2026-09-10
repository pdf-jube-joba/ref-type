# Refinement を含む generation

このページでは、型の一意性を使わずに lambda・subset・RunStep constructor の
導入時の型を回収する。対象は datatype と Box を除いた Set/Prop core である。

<a id="auxiliary-system"></a>

## 証明用の体系

[合流性](confluence.md#auxiliary-reduction)の補助 reduction を
\(\rightsquigarrow\)、その同じ family 内での同値閉包を \(\equiv_+\) とする。
\(\mathcal S_+\) は、現行 core の conversion の側条件だけを
\(\equiv_0\) から \(\equiv_+\) へ広げた証明用の体系である。
構文、rule label、その他の typing・provability 規則は同じである。
この定義は system.md の規則を変更しない。

\[
\Gamma\vdash_0 J\Longrightarrow\Gamma\vdash_+J,\qquad
\Gamma\vDash_0P\Longrightarrow\Gamma\vDash_+P.
\tag{Core-inclusion}
\]
証明は元の有限導出の同時帰納法。\(\Rightarrow_0\subseteq\rightsquigarrow\)
なので、conversion の場合にも同じ premise から結論できる。

補助 reduction は代入で保存される。beta は代入の合成則、他の root は
metavariable への一様な代入による。従って[typing](typing.md)の
weakening、Substitution、Regularity、Prop-conversion、Context-conversion の
証明は、すべて \(\mathcal S_+\) にも適用できる。
これらの補題は SR やモデルの健全性を仮定しない。

## 補助 conversion の injectivity

**補題。** 次が成り立つ。
\[
\begin{aligned}
\Ty(A,S)\equiv_+\Ty(B,T)&\Longrightarrow A\equiv_+B,\ S\equiv_+T,\\
\Power A\equiv_+\Power B&\Longrightarrow A\equiv_+B,\\
\operatorname{RunStep}(A,B)\equiv_+\operatorname{RunStep}(C,D)
 &\Longrightarrow A\equiv_+C,\ B\equiv_+D,\\
\Pi_r x:A.B\equiv_+\Pi_{r'}x:C.D
 &\Longrightarrow r=r',\ A\equiv_+C,\ B\equiv_+D.
\end{aligned}
\tag{Aux-injectivity}
\]
最後の式では binder を alpha-renaming で揃える。
Ty、Power、RunStep、product の異なる head 同士は \(\equiv_+\) でない。

**証明。** \(\rightsquigarrow\) の合流性から、同値な二項は共通簡約先を持つ。
表示した四 constructor は root reduction を持たないので、各側の有限簡約列は
外側の constructor を保つ。共通簡約先の対応する引数までの列が、
引数同士の \(\equiv_+\) を与える。product の label も簡約で変わらない。□

この結論は \(\equiv_+\) についての injectivity であり、
引数の \(\equiv_0\) までは結論しない。

<a id="refinement-root"></a>

## 型の refinement root

各型 family ごとに、raw 型の \(\equiv_+\) 同値類を考える。
Ty の形の代表元を持つ類に対してのみ、部分関数
\[
\operatorname{parent}([\Ty(A,S)]):=[A]
\]
を定める。Aux-injectivity により代表元の選択によらない。
Ty と head が異なる product・Power・RunStep の類には parent がない。

parent を有限回たどって parent のない類 \(R\) に着く場合、
\(\operatorname{root}([T])=R\) と書く。
全 raw 型についてこの操作が停止するとは仮定しない。

**補題。** \(\operatorname{root}(C)=R\) なら、
parent の一辺をどちらの向きに移動しても root は存在し、\(R\) のままである。

**証明。** \(\operatorname{parent}(C)=D\) なら、C から R への有限列の先頭を
取り除けば D から R への列を得る。
\(\operatorname{parent}(D)=C\) なら D を先頭に追加すればよい。
parent は部分関数なので終点は一意である。□

ここでは \(\Ty(A,S)\) を A と定義的に同一視していない。
root は、型付けの導出中で refinement の導入・除去を追跡するためだけの補助操作である。

## 導入規則までの追跡

**補題。** subject が文字どおり lambda、subset、continue、finish のいずれかである
\(\Gamma\vdash_+e:T\) の導出から、対応する導入規則の instance とその全 premise を
\(\Gamma\) のもとで回収できる。その導入規則の結論の型を \(T_{\mathrm{in}}\) とすると
\[
\operatorname{root}([T])=[T_{\mathrm{in}}].
\tag{Introduction-root}
\]

**証明。** subject を保つ premise を遡る。
対応する導入規則に着くまで、現れ得る規則は weak、conversion、
subset intro、subset weak だけである。型演算子の lambda には後二者も適用されない。
それ以外の規則は結論の subject の外側の constructor が異なる。
元の導出は有限なので必ず導入規則に着く。

導入時の型はそれぞれ product、Power、RunStep、RunStep であり、
その類には parent がない。その後の導出を結論へ向かって戻ると、
conversion は同値類を変えず、subset intro/weak は parent の一辺を逆向き／順向きに移る。
上の補題により root は保たれる。weak は型の raw 構文を変えない。
導入時の context が \(\Gamma\) の prefix なら、全 premise を weakening する。
局所 binder は \(\Gamma\) の変数と異なる名前に取り直す。□

従って、表示型 T が product・Power・RunStep なら
\(T\equiv_+T_{\mathrm{in}}\) である。
subset intro と subset weak が何回交互に現れても、この結論は変わらない。

<a id="generation"></a>

## 消去に使う形の generation

**定理。** 以下はすべて \(\mathcal S_+\) の判断である。

1. \(\Gamma\vdash_+\lambda_r x:C.m:\Pi_r x:A.B\) なら、ある D について
   \[
   \Gamma\vdash_+C:\sigma_1,\quad
   \Gamma,x:C\vdash_+D:\sigma_2,\quad
   \Gamma,x:C\vdash_+m:D,\quad
   C\equiv_+A,\quad D\equiv_+B,
   \]
   ただし \(r=(\sigma_1,\sigma_2,\sigma_3)\)。
2. \(\Gamma\vdash_+\{x:C\mid P\}:\Power A\) なら
   \[
   \Gamma\vdash_+C:*^s_i,\quad
   \Gamma,x:C\vdash_+P:*^p,\quad C\equiv_+A.
   \]
3. \(\Gamma\vdash_+\operatorname{continue}_{C,D}(a):\operatorname{RunStep}(A,B)\) なら
   \[
   \Gamma\vdash_+C:*^s_i,\quad\Gamma\vdash_+D:*^s_i,\quad
   \Gamma\vdash_+a:C,\quad C\equiv_+A,\quad D\equiv_+B.
   \]
4. finish については、第三項の argument typing が
   \(\Gamma\vdash_+b:D\) になる。

**証明。** Introduction-root で導入時の型と表示型の同値を得て、
Aux-injectivity を適用する。formation と body/argument typing は回収した
導入規則の premise そのものである。□

消去規則の premise から A、B の formation も与えられているときは、
ここで得た conversion と Context-conversion、Substitution により、
必要な表示型で argument/body を扱える。
この使い方を[補助体系の subject reduction](subject_reduction.md)で示す。
