# Core calculus
> [! note]
> この block quote は削除しないし追記しないでください。
> ここは体系を簡潔に述べるところです。
> 次のことをしないでください。
> 会話由来の「○○しない」を書かない
> 過去の状態から変更した理由を書かない
> 体系の性質/定理を書かない

## Sort

- \(\mathcal B_{sp}=\{*^s_i\mid i\in\mathbb N\}\cup\{*^p\}\)
- \(\mathcal B_{pr}=\{*^v_i,*^c_i\mid i\in\mathbb N\}\)
- \(\mathcal B=\mathcal B_{sp}\cup\mathcal B_{pr}\)
- \(\mathcal S_{sp}=\mathcal B_{sp}\cup\kappa(\mathcal B_{sp})\)
- \(\kappa(*^s_i)=\square^s_i\)
- \(\kappa(*^p)=\square^p\)
- \(\kappa(*^q_i)=\square^q_i\quad(q\in\{v,c\})\)
- \(\mathcal S=\mathcal B\cup\kappa(\mathcal B)\)
- \(\mathcal A=\{(b,\kappa(b))\mid b\in\mathcal B\}\)
- \(i,j,k,h\in\mathbb N\)
- \(q,q'\in\{v,c\}\)
- \(b\in\mathcal B\)
- \(\sigma,\sigma_1,\sigma_2,\sigma_3\in\mathcal S\)
- \(\mathcal S_{pr}:=\mathcal B_{pr}\cup\kappa(\mathcal B_{pr})\)

### Product signature

\[
\begin{aligned}
\mathcal R_s=\bigcup_{i,j\in\mathbb N}\{&
(*^s_i,*^s_j,*^s_{\max(i,j)}),\\
&(*^s_i,\square^s_j,\square^s_{\max(i,j)}),\\
&(\square^s_i,\square^s_j,\square^s_{\max(i,j)}),\\
&(\square^s_i,*^s_j,*^s_{\max(i+1,j)})\}.
\end{aligned}
\]

\[
\begin{aligned}
\mathcal R_{sp}={}&\mathcal R_s\\
&\cup\{(*^p,*^p,*^p),(\square^p,*^p,*^p),
               (\square^p,\square^p,\square^p)\}\\
&\cup\bigcup_i\{(\sigma,\tau,\tau)\mid
  \sigma\in\{*^s_i,\square^s_i\},\
  \tau\in\{*^p,\square^p\}\}.
\end{aligned}
\]

\[
\begin{aligned}
\mathcal R_{pr}=\bigcup_{i,j}\{&
(*^v_i,*^c_j,*^c_{\max(i,j)})\}\\
\cup\bigcup_{q,i,j}\{&
(\square^q_i,*^c_j,*^c_{\max(i+1,j)})\}\\
\cup\bigcup_{q,q',i,j}\{&
(\square^q_i,\square^{q'}_j,\square^{q'}_{\max(i,j)})\}.
\end{aligned}
\]

- \(\mathcal R:=\mathcal R_{sp}\cup\mathcal R_{pr}\)

level は non-cumulative な構文添字とし、level パラメータ付き規則・宣言は schema とする。

### Rule label

- \(s^{i,j}:=(*^s_i,*^s_j,*^s_{\max(i,j)})\)
- \(r^{i,j}_{vc}:=(*^v_i,*^c_j,*^c_{\max(i,j)})\)
- \(r^{q;i,j}_{tc}:=(\square^q_i,*^c_j,*^c_{\max(i+1,j)})\)
- \(p_i:=(*^s_i,\square^p,\square^p)\)
- \(a_i:=(*^s_i,*^p,*^p)\)
- \(o:=(*^p,*^p,*^p)\)
- \(h_{i,\sigma}:=(*^s_i,\sigma,\tau)\in\mathcal R_{sp}\)
- \(A\to_r B:=\Pi_r z:A.B\quad(z\notin\operatorname{FV}(B))\)

## Term, Context, Judgement

### Term

#### Syntax family

三構文を相互帰納的に生成し、alpha 同値で同一視する。

| category | syntax | judgement |
| --- | --- | --- |
| term | \(t\in\mathsf{Tm}_b\) | \(H\vdash t:A\), \(H\vdash A:b\) |
| type constructor | \(A\in\mathsf{Ty}_b\) | \(H\vdash A:K\), \(H\vdash K:\kappa(b)\) |
| kind | \(K\in\mathsf{Kd}_b\) | \(H\vdash K:\kappa(b)\) |

- \(\mathsf F_b\cap\mathsf G_{b'}=\varnothing\quad((\mathsf F,b)\ne(\mathsf G,b'))\)
- \(\mathsf F,\mathsf G\in\{\mathsf{Tm},\mathsf{Ty},\mathsf{Kd}\}\)

| \(\sigma\) | \(\mathsf E_\sigma\) | \(\mathsf C_\sigma\) | variable \(z^\sigma\) |
| --- | --- | --- | --- |
| \(b\) | \(\mathsf{Tm}_b\) | \(\mathsf{Ty}_b\) | \(x_b\) |
| \(\kappa(b)\) | \(\mathsf{Ty}_b\) | \(\mathsf{Kd}_b\) | \(X_b\) |

- \(\mathsf{Var}_{sp}:=\{x_b,X_b\mid b\in\mathcal B_{sp}\}\)
- \(\mathsf{Var}_{pr}:=\{x_{*^v_i},X_{*^q_i}\mid i\in\mathbb N,\ q\in\{v,c\}\}\)
- \(\mathsf{Var}_{sp}\cap\mathsf{Var}_{pr}=\varnothing\)

#### Basic constructor

- \(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R\)

| category | definition | family | other |
| --- | --- | --- | --- |
| base kind | \(b\) | \(\mathsf{Kd}_b\) | |
| term variable | \(x_b\) | \(\mathsf{Tm}_b\) | \(x_b\in\mathsf{Var}_{sp}\cup\mathsf{Var}_{pr}\) |
| type variable | \(X_b\) | \(\mathsf{Ty}_b\) | |
| dependent product | \(\Pi_r z^{\sigma_1}:A.B\) | \(\mathsf C_{\sigma_3}\) | \(A\in\mathsf C_{\sigma_1}\), \(B\in\mathsf C_{\sigma_2}\) |
| lambda abstraction | \(\lambda_r z^{\sigma_1}:A.e\) | \(\mathsf E_{\sigma_3}\) | \(A\in\mathsf C_{\sigma_1}\), \(e\in\mathsf E_{\sigma_2}\) |
| application | \(f@_r a\) | \(\mathsf E_{\sigma_2}\) | \(f\in\mathsf E_{\sigma_3}\), \(a\in\mathsf E_{\sigma_1}\) |

- \(r=r^{i,j}_{vc}\Longrightarrow z\notin\operatorname{FV}(B)\)
- \(P\in\mathsf{Ty}_{*^q_i}\cup\mathsf{Kd}_{*^q_i} \Longrightarrow\operatorname{FV}(P)\subseteq\{X_{*^{q'}_j}\mid q'\in\{v,c\},\ j\in\mathbb N\}\)

#### Set/Prop

- \(A,B,X,T\in\mathsf{Ty}_{*^s_i}\)
- \(a,b,u,f\in\mathsf{Tm}_{*^s_i}\)
- \(P\in\mathsf{Ty}_{*^p}\)
- \(g\in\mathsf{Tm}_{*^p}\)

| category | definition | family |
| --- | --- | --- |
| power set | \(\Power A\) | \(\mathsf{Ty}_{*^s_i}\) |
| type lift | \(\Ty(A,u)\) | \(\mathsf{Ty}_{*^s_i}\) |
| refinement | \(\{x_{*^s_i}:A\mid P\}\) | \(\mathsf{Tm}_{*^s_i}\) |
| predicate | \(\Pred(A,u,a)\) | \(\mathsf{Ty}_{*^p}\) |
| equality | \(a=b\) | \(\mathsf{Ty}_{*^p}\) |
| existence | \(\exists A\) | \(\mathsf{Ty}_{*^p}\) |
| proof mark | \(\Proof P\) | \(\mathsf{Tm}_{*^p}\) |
| take set | \(\Take^s_i(X,T,f)\) | \(\mathsf{Tm}_{*^s_i}\) |
| take prop | \(\Take^p_i(X,P,g)\) | \(\mathsf{Tm}_{*^p}\) |
| run step | \(\operatorname{RunStep}(A,B)\) | \(\mathsf{Ty}_{*^s_i}\) |
| continue | \(\operatorname{continue}_{A,B}(a)\) | \(\mathsf{Tm}_{*^s_i}\) |
| finish | \(\operatorname{finish}_{A,B}(b)\) | \(\mathsf{Tm}_{*^s_i}\) |
| accessibility | \(\operatorname{Acc}_{A,B}(f,a)\) | \(\mathsf{Ty}_{*^p}\) |
| run | \(\operatorname{run}_{A,B}(f,a)\) | \(\mathsf{Tm}_{*^s_i}\) |
| run case | \(\operatorname{runCase}_{A,B}(f,a,u)\) | \(\mathsf{Tm}_{*^s_i}\) |

- \(\operatorname{prec}^{\sigma}_{\operatorname{RunStep}(A,B)}(x_{*^s_i}.P,c,d,r)\in\mathsf E_\sigma\)
  - premises: \(A,B\in\mathsf{Ty}_{*^s_i}\), \(P\in\mathsf C_\sigma\), \(c,d\in\mathsf E_\tau\), \(r\in\mathsf{Tm}_{*^s_i}\), \(h_{i,\sigma}=(*^s_i,\sigma,\tau)\in\mathcal R_{sp}\)

#### Program

| category | notation | family |
| --- | --- | --- |
| value type constructor | \(A,B\) | \(\mathsf{Ty}_{*^v_i}\) |
| computation type constructor | \(\underline B\) | \(\mathsf{Ty}_{*^c_j}\) |
| value | \(V,W\) | \(\mathsf{Tm}_{*^v_i}\) |
| computation | \(M,N\) | \(\mathsf{Tm}_{*^c_j}\) |
| program type constructor | \(P\) | \(\mathsf{Ty}_{*^q_i}\) |
| program | \(p\) | \(\mathsf{Tm}_{*^q_i}\) |

- \(A,B\in\mathsf{Ty}_{*^v_i}\)
- \(\underline C\in\mathsf{Ty}_{*^c_i}\)
- \(V,W\in\mathsf{Tm}_{*^v_i}\)
- \(M\in\mathsf{Tm}_{*^c_i}\)
- \(N\in\mathsf{Tm}_{*^c_j}\)

| category | definition | family |
| --- | --- | --- |
| returner type | \(F A\) | \(\mathsf{Ty}_{*^c_i}\) |
| thunk type | \(U\underline C\) | \(\mathsf{Ty}_{*^v_i}\) |
| run step type | \(\operatorname{RunStep}(A,B)\) | \(\mathsf{Ty}_{*^v_i}\) |
| return | \(\operatorname{return}(V)\) | \(\mathsf{Tm}_{*^c_i}\) |
| thunk | \(\operatorname{thunk}(M)\) | \(\mathsf{Tm}_{*^v_i}\) |
| force | \(\operatorname{force}(V)\) | \(\mathsf{Tm}_{*^c_i}\) |
| sequence | \(M\ \operatorname{to}\ x_{*^v_i}:A\ \operatorname{in}\ N\) | \(\mathsf{Tm}_{*^c_j}\) |
| value let | \(\operatorname{let}^v x_{*^v_i}:A=V\ \operatorname{in}\ N\) | \(\mathsf{Tm}_{*^c_j}\) |
| continue | \(\operatorname{continue}_{A,B}(V)\) | \(\mathsf{Tm}_{*^v_i}\) |
| finish | \(\operatorname{finish}_{A,B}(V)\) | \(\mathsf{Tm}_{*^v_i}\) |
| run | \(\operatorname{run}_{A,B}(V,W)\) | \(\mathsf{Tm}_{*^c_i}\) |
| run case | \(\operatorname{runCase}_{A,B}(V,W,M)\) | \(\mathsf{Tm}_{*^c_i}\) |

#### Boxed Program

- \(P\in\mathsf{Ty}_{*^q_i}\)
- \(p\in\mathsf{Tm}_{*^q_i}\)
- \(t\in\mathsf{Tm}_{*^s_i}\)
- \(A\in\mathsf{Ty}_{*^v_i}\)
- \(\underline B\in\mathsf{Ty}_{*^c_j}\)
- \(K\in\mathsf{Kd}_{*^q_i}\)

| category | definition | family | other |
| --- | --- | --- | --- |
| boxed Program type | \(\operatorname{Box}(P)\) | \(\mathsf{Ty}_{*^s_i}\) | |
| boxed Program | \(\operatorname{box}_P(p)\) | \(\mathsf{Tm}_{*^s_i}\) | |
| force boxed Program | \(\operatorname{Force}_P(t)\) | \(\mathsf{Tm}_{*^s_i}\) | |
| boxed value application | \(\operatorname{bapp}_{A,\underline B}(f,a)\) | \(\mathsf{Tm}_{*^s_j}\) | \(f\in\mathsf{Tm}_{*^s_{\max(i,j)}}\), \(a\in\mathsf{Tm}_{*^s_i}\) |
| boxed type application | \(\operatorname{btapp}_{X_{*^q_i}:K,\underline B}(f,P)\) | \(\mathsf{Tm}_{*^s_j}\) | \(f\in\mathsf{Tm}_{*^s_{\max(i+1,j)}}\) |

#### Binder と substitution

| constructor | bound variable | scope |
| --- | --- | --- |
| \(\Pi_r z:A.B\) | \(z\) | \(B\) |
| \(\lambda_r z:A.e\) | \(z\) | \(e\) |
| \(\{x:A\mid P\}\) | \(x\) | \(P\) |
| \(\operatorname{prec}^{\sigma}_D(x.P,c,d,r)\) | \(x\) | \(P\) |
| \(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N\) | \(x\) | \(N\) |
| \(\operatorname{let}^v x:A=V\ \operatorname{in}\ N\) | \(x\) | \(N\) |
| \(\operatorname{btapp}_{X:K,\underline B}(f,P)\) | \(X\) | \(\underline B\) |
| \(\operatorname{case}^d_B(t;\overline{C_l^d(\vec x_l)\mapsto e_l})\) | \(\vec x_l\) | \(e_l\) |

\(e[z:=a]\) は三構文・型注釈・型引数を同時に辿る capture-avoiding substitution とする。

- \(\mathsf F\in\{\mathsf{Tm}_b,\mathsf{Ty}_b,\mathsf{Kd}_b\mid b\in\mathcal B\}\)
- \(e[z:=a]\in\mathsf F\)
  - premises: \(e\in\mathsf F\), \(z\in\mathsf E_\sigma\), \(a\in\mathsf E_\sigma\)

### Context と judgement

- \(\mathsf{Ctx}_{sp}\ni\Gamma::=\varnothing\mid\Gamma,x_b:A\mid\Gamma,X_b:K\quad(b\in\mathcal B_{sp})\)
- \(\mathsf{Ctx}_{pr}\ni\Delta::=\varnothing\mid\Delta,X_{*^q_i}:K\mid\Delta,x_{*^v_i}:A\)
- \(\mathsf{Ctx}_{ty}\ni\Theta::=\varnothing\mid\Theta,X_{*^q_i}:K\)
- \(\operatorname{TyCtx}(\varnothing):=\varnothing\)
- \(\operatorname{TyCtx}(\Delta,X:K):=\operatorname{TyCtx}(\Delta),X:K\)
- \(\operatorname{TyCtx}(\Delta,x:A):=\operatorname{TyCtx}(\Delta)\)
- \(\Theta:=\operatorname{TyCtx}(\Delta)\)
- \(H::=\Gamma\mid\Delta\mid\Theta\)

| category | judgement | syntax |
| --- | --- | --- |
| well formed context | \(\operatorname{WF}(H)\) | |
| kind formation | \(H\vdash K:\kappa(b)\) | \(K\in\mathsf{Kd}_b\) |
| type constructor typing | \(H\vdash A:K\) | \(A\in\mathsf{Ty}_b\), \(K\in\mathsf{Kd}_b\) |
| term typing | \(H\vdash t:A\) | \(t\in\mathsf{Tm}_b\), \(A\in\mathsf{Ty}_b\) |
| provable | \(\Gamma\vDash P\) | \(P\in\mathsf{Ty}_{*^p}\) |
| well-terminated Program | \(\Delta\Vdash p:P\) | \(p\in\mathsf{Tm}_{*^q_i}\), \(P\in\mathsf{Ty}_{*^q_i}\) |

- \(\Delta\vdash e:A\;:\Longleftrightarrow\; \operatorname{TyCtx}(\Delta)\vdash e:A \quad(e\in\mathsf{Ty}_{*^q_i}\cup\mathsf{Kd}_{*^q_i})\)

## reduction

### Compatible closure

- \(\Rightarrow_{\mathsf F}\;\subseteq\;\mathsf F\times\mathsf F\)
- \(\mathsf F\in\{\mathsf{Tm}_b,\mathsf{Ty}_b,\mathsf{Kd}_b\mid b\in\mathcal B\}\)

\(\Rightarrow_{\mathsf F}\) は以下の root・閉包規則と帰納型の case 規則で生成される最小の関係族とする。
\(C:\mathsf F\rightsquigarrow\mathsf G\) は、次の位置に穴を持つ一穴構文文脈とする。

| output | compatible position |
| --- | --- |
| \(\mathsf{Tm}_b,\mathsf{Ty}_b,\mathsf{Kd}_b\), \(b\in\mathcal B_{sp}\) | 全 Set/Prop 引数（binder 注釈・body を含む） |
| \(\mathsf{Ty}_b,\mathsf{Kd}_b\), \(b\in\mathcal B_{pr}\) | 全 Program type/kind 引数（binder 注釈・body を含む） |

- \(C[e]\Rightarrow_{\mathsf G}C[e']\)
  - premises: \(e\Rightarrow_{\mathsf F}e'\), \(C:\mathsf F\rightsquigarrow\mathsf G\)

### Basic beta

- \((\lambda_r z:A.e)@_r a\Rightarrow_{\mathsf E_{\sigma_2}}e[z:=a]\)
  - premises: \(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R\), \(r\in\mathcal R_{sp}\ \lor\ \sigma_2\in\kappa(\mathcal B_{pr})\)

### Set/Prop

- \(\Pred(A,\{x:B\mid P\},t) \Rightarrow_{\mathsf{Ty}_{*^p}}(\lambda_{p_i}x:B.P)@_{p_i}t\)
- \(\operatorname{prec}^{\sigma}_{\operatorname{RunStep}(A,B)}(x.P,c,d,\operatorname{continue}_{A,B}(a)) \Rightarrow_{\mathsf E_\sigma}c@_{h_{i,\sigma}}a\)
- \(\operatorname{prec}^{\sigma}_{\operatorname{RunStep}(A,B)}(x.P,c,d,\operatorname{finish}_{A,B}(b)) \Rightarrow_{\mathsf E_\sigma}d@_{h_{i,\sigma}}b\)
- \(\operatorname{run}_{A,B}(f,a) \Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{runCase}_{A,B}(f,a,f@_{s^{i,i}}a)\)
- \(\operatorname{runCase}_{A,B}(f,a,\operatorname{continue}_{A,B}(a')) \Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{run}_{A,B}(f,a')\)
- \(\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{A,B}(b)) \Rightarrow_{\mathsf{Tm}_{*^s_i}}b\)

### Program

#### Evaluation context

- \(E_h^j:\mathsf{Tm}_{*^c_h}\rightsquigarrow\mathsf{Tm}_{*^c_j}\)
- \([\,]\in E_h^h\)
- \(E@_{r^{i,j}_{vc}}V\in E_h^j\)
  - premises: \(E\in E_h^{\max(i,j)}\), \(V\in\mathsf{Tm}_{*^v_i}\)
- \(E@_{r^{q;i,j}_{tc}}P\in E_h^j\)
  - premises: \(E\in E_h^{\max(i+1,j)}\), \(P\in\mathsf{Ty}_{*^q_i}\)
- \(E\ \operatorname{to}\ x_{*^v_i}:A\ \operatorname{in}\ N\in E_h^j\)
  - premises: \(E\in E_h^i\), \(A\in\mathsf{Ty}_{*^v_i}\), \(N\in\mathsf{Tm}_{*^c_j}\)
- \(\operatorname{runCase}_{A,B}(V,W,E)\in E_h^i\)
  - premises: \(E\in E_h^i\), \(A,B\in\mathsf{Ty}_{*^v_i}\), \(V,W\in\mathsf{Tm}_{*^v_i}\)
- \(E[M]\Rightarrow_{\mathsf{Tm}_{*^c_j}}E[M']\)
  - premises: \(M\Rightarrow_{\mathsf{Tm}_{*^c_h}}M'\), \(E\in E_h^j\)

#### Computation root

- \(\operatorname{force}(\operatorname{thunk}(M))\Rightarrow_{\mathsf{Tm}_{*^c_i}}M\)
- \((\lambda_{r^{i,j}_{vc}}x:A.M)@_{r^{i,j}_{vc}}V\Rightarrow_{\mathsf{Tm}_{*^c_j}}M[x:=V]\)
- \((\lambda_{r^{q;i,j}_{tc}}X:K.M)@_{r^{q;i,j}_{tc}}P\Rightarrow_{\mathsf{Tm}_{*^c_j}}M[X:=P]\)
- \(\operatorname{return}(V)\ \operatorname{to}\ x:A\ \operatorname{in}\ N \Rightarrow_{\mathsf{Tm}_{*^c_j}}N[x:=V]\)
- \(\operatorname{let}^v x:A=V\ \operatorname{in}\ N \Rightarrow_{\mathsf{Tm}_{*^c_j}}N[x:=V]\)
- \(\operatorname{run}_{A,B}(f,a) \Rightarrow_{\mathsf{Tm}_{*^c_i}}\operatorname{runCase}_{A,B}(f,a,\operatorname{force}(f)@_{r^{i,i}_{vc}}a)\)
- \(\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a'))) \Rightarrow_{\mathsf{Tm}_{*^c_i}}\operatorname{run}_{A,B}(f,a')\)
- \(\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b))) \Rightarrow_{\mathsf{Tm}_{*^c_i}}\operatorname{return}(b)\)
- \(\Rightarrow_{\mathsf{Tm}_{*^v_i}}:=\varnothing\)

### Boxed Program

| category | reduction | other |
| --- | --- | --- |
| box step | \(\operatorname{box}_{\underline B}(M)\Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{box}_{\underline B}(M')\) | \(M\Rightarrow_{\mathsf{Tm}_{*^c_i}}M'\) |
| force box | \(\operatorname{Force}_P(\operatorname{box}_P(p))\Rightarrow_{\mathsf{Tm}_{*^s_i}}\operatorname{RfTerm}(p)\) | \(\varnothing\vdash P:*^q_i\)<br>\(\varnothing\vdash p:P\)<br>\(\nexists p'.\ p\Rightarrow_{\mathsf{Tm}_{*^q_i}}p'\) |
| boxed value application | \(\operatorname{bapp}_{A,\underline B}(\operatorname{box}_{A\to_{r^{i,j}_{vc}}\underline B}(M),\operatorname{box}_A(V))\Rightarrow_{\mathsf{Tm}_{*^s_j}}\operatorname{box}_{\underline B}(M@_{r^{i,j}_{vc}}V)\) | |
| boxed type application | \(\operatorname{btapp}_{X:K,\underline B}(\operatorname{box}_{\Pi_{r^{q;i,j}_{tc}}X:K.\underline B}(M),P)\Rightarrow_{\mathsf{Tm}_{*^s_j}}\operatorname{box}_{\underline B[X:=P]}(M@_{r^{q;i,j}_{tc}}P)\) | |

### definitional equality

- \(\mathsf F\in\{\mathsf{Ty}_b,\mathsf{Kd}_b\mid b\in\mathcal B\}\)
- \(\equiv_{\mathsf F}:=(\Rightarrow_{\mathsf F}\cup\Leftarrow_{\mathsf F})^*\)
- \(A\equiv_{\mathsf F}B\;:\Longleftrightarrow\; \exists n\in\mathbb N,\ A_0,\ldots,A_n\in\mathsf F.\ A_0=A\land A_n=B\land \forall l<n.\ (A_l\Rightarrow_{\mathsf F}A_{l+1}\lor A_{l+1}\Rightarrow_{\mathsf F}A_l)\)

## derivation

### Context と basic typing

typing・provability 規則は、出現する context の \(\operatorname{WF}\) と構文 family の条件を前提とする。導出は有限木とする。

- \(H::e:=H,e\)
- \(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R\)
- \(\mathsf{Ctx}_{ty}\subseteq\mathsf{Ctx}_{pr}\)
- \(d\in\{sp,pr\}\)
- \(H\in\mathsf{Ctx}_d\Longrightarrow \bigl(b\in\mathcal B_d\ \land\ \sigma\in\mathcal S_d\ \land\ r\in\mathcal R_d\bigr)\)
- \(H\vdash e:A\quad(e\in\mathsf E_\sigma,\ A\in\mathsf C_\sigma)\)
- \(H\vdash K:\kappa(b)\quad(K\in\mathsf{Kd}_b)\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | \(\operatorname{WF}(\varnothing)\) | | |
| axiom | \(H\vdash b:\kappa(b)\) | \(\operatorname{WF}(H)\) | \((b,\kappa(b))\in\mathcal A\) |
| start | \(\operatorname{WF}(H,z^\sigma:A)\) | \(\operatorname{WF}(H)\)<br>\(H\vdash A:\sigma\) | \(z^\sigma\notin\operatorname{dom}(H)\)<br>\(H,z^\sigma:A\in\mathsf{Ctx}_d\) |
| variable | \(H,z^\sigma:A\vdash z^\sigma:A\) | \(\operatorname{WF}(H,z^\sigma:A)\) | |
| weak | \(H,z^\sigma:A\vdash J\) | \(H\vdash J\)<br>\(\operatorname{WF}(H,z^\sigma:A)\) | \(z^\sigma\notin\operatorname{FV}(J)\) |
| provable weak | \(\Gamma,z^\sigma:A\vDash P\) | \(\Gamma\vDash P\)<br>\(\operatorname{WF}(\Gamma,z^\sigma:A)\) | \(z^\sigma\notin\operatorname{FV}(P)\) |
| conversion | \(H\vdash e:B\) | \(H\vdash e:A\)<br>\(H\vdash A:\sigma\)<br>\(H\vdash B:\sigma\) | \(A\equiv_{\mathsf C_\sigma}B\) |
| dep form | \(H\vdash\Pi_r z:A.B:\sigma_3\) | \(H\vdash A:\sigma_1\)<br>\(H,z:A\vdash B:\sigma_2\) | \(z\notin\operatorname{dom}(H)\) |
| dep intro | \(H\vdash\lambda_r z:A.e:\Pi_r z:A.B\) | \(H\vdash A:\sigma_1\)<br>\(H,z:A\vdash B:\sigma_2\)<br>\(H,z:A\vdash e:B\) | \(z\notin\operatorname{dom}(H)\) |
| dep elim | \(H\vdash f@_r a:B[z:=a]\) | \(H\vdash A:\sigma_1\)<br>\(H,z:A\vdash B:\sigma_2\)<br>\(H\vdash f:\Pi_r z:A.B\)<br>\(H\vdash a:A\) | \(z\notin\operatorname{dom}(H)\) |

### Set/Prop

#### provable

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| provable | \(\Gamma\vDash P\) | \(\Gamma\vdash P:*^p\)<br>\(\Gamma\vdash t:P\) | |
| proof term | \(\Gamma\vdash\Proof P:P\) | \(\Gamma\vDash P\) | |

#### power set, subset

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| power set form | \(\Gamma\vdash\Power A:*^s_i\) | \(\Gamma\vdash A:*^s_i\) | |
| type lift | \(\Gamma\vdash\Ty(A,S):*^s_i\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash S:\Power A\) | |
| predicate | \(\Gamma\vdash\Pred(A,S,t):*^p\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash S:\Power A\)<br>\(\Gamma\vdash t:A\) | |
| subset form | \(\Gamma\vdash\{x_{*^s_i}:A\mid P\}:\Power A\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma,x_{*^s_i}:A\vdash P:*^p\) | \(x_{*^s_i}\notin\operatorname{dom}(\Gamma)\) |
| subset intro | \(\Gamma\vdash t:\Ty(A,S)\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash S:\Power A\)<br>\(\Gamma\vdash t:A\)<br>\(\Gamma\vDash\Pred(A,S,t)\) | |
| subset weak | \(\Gamma\vdash t:A\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash S:\Power A\)<br>\(\Gamma\vdash t:\Ty(A,S)\) | |
| subset prop | \(\Gamma\vDash\Pred(A,S,t)\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash S:\Power A\)<br>\(\Gamma\vdash t:\Ty(A,S)\) | |

#### equality

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| id form | \(\Gamma\vdash a=b:*^p\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash a:A\)<br>\(\Gamma\vdash b:A\) | |
| id intro | \(\Gamma\vDash a=a\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash a:A\) | |
| id elim | \(\Gamma\vDash(\lambda_{p_i}x:A.P)@_{p_i}b\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash a:A\)<br>\(\Gamma\vdash b:A\)<br>\(\Gamma\vDash a=b\)<br>\(\Gamma,x:A\vdash P:*^p\)<br>\(\Gamma\vDash(\lambda_{p_i}x:A.P)@_{p_i}a\) | \(x\notin\operatorname{dom}(\Gamma)\) |

#### choice

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| exists form | \(\Gamma\vdash\exists T:*^p\) | \(\Gamma\vdash T:*^s_i\) | |
| exists intro | \(\Gamma\vDash\exists T\) | \(\Gamma\vdash T:*^s_i\)<br>\(\Gamma\vdash e:T\) | |
| take elim set | \(\Gamma\vdash\Take^s_i(X,T,f):T\) | \(\Gamma\vdash X:*^s_i\)<br>\(\Gamma\vdash T:*^s_i\)<br>\(\Gamma\vdash X\to_{s^{i,i}}T:*^s_i\)<br>\(\Gamma\vdash f:X\to_{s^{i,i}}T\)<br>\(\Gamma\vDash\exists X\)<br>\(\Gamma\vDash\Pi_{a_i}x_1:X.\Pi_{a_i}x_2:X.\,(f@_{s^{i,i}}x_1=f@_{s^{i,i}}x_2)\) | \(\{x_1,x_2\}\cap\operatorname{dom}(\Gamma)=\varnothing\)<br>\(x_1\ne x_2\) |
| take elim prop | \(\Gamma\vdash\Take^p_i(X,P,g):P\) | \(\Gamma\vdash X:*^s_i\)<br>\(\Gamma\vdash P:*^p\)<br>\(\Gamma\vdash X\to_{a_i}P:*^p\)<br>\(\Gamma\vdash g:X\to_{a_i}P\)<br>\(\Gamma\vDash\exists X\) | |
| take equal | \(\Gamma\vDash\Take^s_i(X,T,f)=f@_{s^{i,i}}t\) | \(\Gamma\vdash X:*^s_i\)<br>\(\Gamma\vdash T:*^s_i\)<br>\(\Gamma\vdash X\to_{s^{i,i}}T:*^s_i\)<br>\(\Gamma\vdash f:X\to_{s^{i,i}}T\)<br>\(\Gamma\vdash\Take^s_i(X,T,f):T\)<br>\(\Gamma\vdash t:X\) | |

#### RunStep

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| run step form | \(\Gamma\vdash\operatorname{RunStep}(A,B):*^s_i\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\) | |
| continue intro | \(\Gamma\vdash\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B)\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash a:A\) | |
| finish intro | \(\Gamma\vdash\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B)\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash b:B\) | |

- \(D:=\operatorname{RunStep}(A,B)\)
- \(h_{i,\sigma}=(*^s_i,\sigma,\tau)\in\mathcal R_{sp}\)
- \(C_P:=\Pi_{h_{i,\sigma}}a:A.P[x:=\operatorname{continue}_{A,B}(a)]\)
- \(D_P:=\Pi_{h_{i,\sigma}}b:B.P[x:=\operatorname{finish}_{A,B}(b)]\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| prec | \(\Gamma\vdash\operatorname{prec}^{\sigma}_D(x.P,c,d,r):P[x:=r]\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash r:D\)<br>\(\Gamma,x_{*^s_i}:D\vdash P:\sigma\)<br>\(\Gamma\vdash C_P:\tau\)<br>\(\Gamma\vdash D_P:\tau\)<br>\(\Gamma\vdash c:C_P\)<br>\(\Gamma\vdash d:D_P\) | \(\{x,a,b\}\cap\operatorname{dom}(\Gamma)=\varnothing\)<br>\(\lvert\{x,a,b\}\rvert=3\) |

#### Acc と run

- \(S_{A,B}:=A\to_{s^{i,i}}\operatorname{RunStep}(A,B)\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| acc form | \(\Gamma\vdash\operatorname{Acc}_{A,B}(f,a):*^p\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash f:S_{A,B}\)<br>\(\Gamma\vdash a:A\) | |
| acc intro | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash f:S_{A,B}\)<br>\(\Gamma\vdash a:A\)<br>\(\Gamma,b:A\vDash(f@_{s^{i,i}}a=\operatorname{continue}_{A,B}(b))\to_o\operatorname{Acc}_{A,B}(f,b)\) | \(b\notin\operatorname{dom}(\Gamma)\) |
| acc descent | \(\Gamma\vDash\operatorname{Acc}_{A,B}(f,b)\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash f:S_{A,B}\)<br>\(\Gamma\vdash a:A\)<br>\(\Gamma\vdash b:A\)<br>\(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\)<br>\(\Gamma\vDash f@_{s^{i,i}}a=\operatorname{continue}_{A,B}(b)\) | |
| run | \(\Gamma\vdash\operatorname{run}_{A,B}(f,a):B\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash f:S_{A,B}\)<br>\(\Gamma\vdash a:A\)<br>\(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\) | |
| run case | \(\Gamma\vdash\operatorname{runCase}_{A,B}(f,a,r):B\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma\vdash f:S_{A,B}\)<br>\(\Gamma\vdash a:A\)<br>\(\Gamma\vdash r:\operatorname{RunStep}(A,B)\)<br>\(\Gamma\vDash\operatorname{Acc}_{A,B}(f,a)\)<br>\(\Gamma\vDash f@_{s^{i,i}}a=r\) | |

### Program

#### Type formation

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| \(F\) form | \(\Theta\vdash F A:*^c_i\) | \(\Theta\vdash A:*^v_i\) | |
| \(U\) form | \(\Theta\vdash U\underline B:*^v_i\) | \(\Theta\vdash\underline B:*^c_i\) | |
| function form | \(\Theta\vdash A\to_{r^{i,j}_{vc}}\underline B:*^c_{\max(i,j)}\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash\underline B:*^c_j\) | |
| run step form | \(\Theta\vdash\operatorname{RunStep}(A,B):*^v_i\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\) | |

#### Program typing

- \(\Theta:=\operatorname{TyCtx}(\Delta)\)
- \(T_{A,B}:=U(A\to_{r^{i,i}_{vc}}F(\operatorname{RunStep}(A,B)))\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| return | \(\Delta\vdash\operatorname{return}(V):F A\) | \(\Theta\vdash A:*^v_i\)<br>\(\Delta\vdash V:A\) | |
| thunk | \(\Delta\vdash\operatorname{thunk}(M):U\underline B\) | \(\Theta\vdash\underline B:*^c_i\)<br>\(\Delta\vdash M:\underline B\) | |
| force | \(\Delta\vdash\operatorname{force}(V):\underline B\) | \(\Theta\vdash\underline B:*^c_i\)<br>\(\Delta\vdash V:U\underline B\) | |
| function intro | \(\Delta\vdash\lambda_{r^{i,j}_{vc}}x:A.M:A\to_{r^{i,j}_{vc}}\underline B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash\underline B:*^c_j\)<br>\(\Delta,x:A\vdash M:\underline B\) | \(x\notin\operatorname{dom}(\Delta)\) |
| function elim | \(\Delta\vdash M@_{r^{i,j}_{vc}}V:\underline B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash\underline B:*^c_j\)<br>\(\Delta\vdash M:A\to_{r^{i,j}_{vc}}\underline B\)<br>\(\Delta\vdash V:A\) | |
| sequence | \(\Delta\vdash M\ \operatorname{to}\ x:A\ \operatorname{in}\ N:\underline B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash\underline B:*^c_j\)<br>\(\Delta\vdash M:F A\)<br>\(\Delta,x:A\vdash N:\underline B\) | \(x\notin\operatorname{dom}(\Delta)\) |
| value let | \(\Delta\vdash\operatorname{let}^v x:A=V\ \operatorname{in}\ N:\underline B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash\underline B:*^c_j\)<br>\(\Delta\vdash V:A\)<br>\(\Delta,x:A\vdash N:\underline B\) | \(x\notin\operatorname{dom}(\Delta)\) |
| continue intro | \(\Delta\vdash\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B)\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Delta\vdash a:A\) | |
| finish intro | \(\Delta\vdash\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B)\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Delta\vdash b:B\) | |
| run | \(\Delta\vdash\operatorname{run}_{A,B}(f,a):F B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Delta\vdash f:T_{A,B}\)<br>\(\Delta\vdash a:A\) | |
| run case | \(\Delta\vdash\operatorname{runCase}_{A,B}(f,a,M):F B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Delta\vdash f:T_{A,B}\)<br>\(\Delta\vdash a:A\)<br>\(\Delta\vdash M:F(\operatorname{RunStep}(A,B))\) | |

#### Polymorphism

- \(k:=\max(i+1,j)\)
- \(r:=r^{q;i,j}_{tc}\)
- \(K\in\mathsf{Kd}_{*^q_i}\)
- \(\underline B\in\mathsf{Ty}_{*^c_j}\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| type product | \(\Theta\vdash\Pi_r X:K.\underline B:*^c_k\) | \(\Theta\vdash K:\square^q_i\)<br>\(\Theta,X:K\vdash\underline B:*^c_j\) | \(X\notin\operatorname{dom}(\Theta)\) |
| type abstraction | \(\Delta\vdash\lambda_r X:K.M:\Pi_r X:K.\underline B\) | \(\Theta\vdash K:\square^q_i\)<br>\(\Theta,X:K\vdash\underline B:*^c_j\)<br>\(\Theta\vdash\Pi_r X:K.\underline B:*^c_k\)<br>\(\Delta,X:K\vdash M:\underline B\) | \(X\notin\operatorname{dom}(\Delta)\) |
| type application | \(\Delta\vdash M@_r P:\underline B[X:=P]\) | \(\Theta\vdash K:\square^q_i\)<br>\(\Theta,X:K\vdash\underline B:*^c_j\)<br>\(\Delta\vdash M:\Pi_r X:K.\underline B\)<br>\(\Theta\vdash P:K\) | \(X\notin\operatorname{dom}(\Delta)\) |

#### Reflection

##### Meta-level maps

名前の反映 \(z\mapsto\bar z\) は単射とする。

- \(\overline{*^q_i}=*^s_i\)
- \(\overline{\square^q_i}=\square^s_i\)
- \(\overline{(\sigma_1,\sigma_2,\sigma_3)} =(\bar\sigma_1,\bar\sigma_2,\bar\sigma_3)\)
- \(\operatorname{RfKind}:\mathsf{Kd}_{*^q_i}\to\mathsf{Kd}_{*^s_i}\)
- \(\operatorname{RfType}:\mathsf{Ty}_{*^q_i}\to\mathsf{Ty}_{*^s_i}\)
- \(\operatorname{RfTerm}:\mathsf{Tm}_{*^q_i}\to\mathsf{Tm}_{*^s_i}\)
- \(\operatorname{Rf}(e):=\operatorname{RfKind}(e)\)
  - \(e\in\mathsf{Kd}_{*^q_i}\)
- \(\operatorname{Rf}(e):=\operatorname{RfType}(e)\)
  - \(e\in\mathsf{Ty}_{*^q_i}\)
- \(\operatorname{Rf}(e):=\operatorname{RfTerm}(e)\)
  - \(e\in\mathsf{Tm}_{*^q_i}\)

##### Basic constructor と context

- \(\operatorname{Rf}(z):=\bar z\)
- \(\operatorname{RfKind}(*^q_i):=*^s_i\)
- \(\operatorname{Rf}(\Pi_r z:A.B):=\Pi_{\bar r}\bar z:\operatorname{Rf}(A).\operatorname{Rf}(B)\)
- \(\operatorname{Rf}(\lambda_r z:A.e):=\lambda_{\bar r}\bar z:\operatorname{Rf}(A).\operatorname{Rf}(e)\)
- \(\operatorname{Rf}(f@_r a):=\operatorname{Rf}(f)@_{\bar r}\operatorname{Rf}(a)\)
- \(\operatorname{RfCtx}(\varnothing):=\varnothing\)
- \(\operatorname{RfCtx}(\Delta,X:K):=\operatorname{RfCtx}(\Delta),\bar X:\operatorname{RfKind}(K)\)
- \(\operatorname{RfCtx}(\Delta,x:A):=\operatorname{RfCtx}(\Delta),\bar x:\operatorname{RfType}(A)\)

##### Program constructor

| constructor | reflection |
| --- | --- |
| \(F A\) | \(\operatorname{RfType}(A)\) |
| \(U\underline B\) | \(\operatorname{RfType}(\underline B)\) |
| \(\operatorname{return}(V)\) | \(\operatorname{RfTerm}(V)\) |
| \(\operatorname{thunk}(M)\) | \(\operatorname{RfTerm}(M)\) |
| \(\operatorname{force}(V)\) | \(\operatorname{RfTerm}(V)\) |
| \(\operatorname{RunStep}(A,B)\) | \(\operatorname{RunStep}(\operatorname{RfType}(A),\operatorname{RfType}(B))\) |
| \(\operatorname{continue}_{A,B}(V)\) | \(\operatorname{continue}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}(\operatorname{RfTerm}(V))\) |
| \(\operatorname{finish}_{A,B}(V)\) | \(\operatorname{finish}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}(\operatorname{RfTerm}(V))\) |
| \(\operatorname{run}_{A,B}(V,W)\) | \(\operatorname{run}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}(\operatorname{RfTerm}(V),\operatorname{RfTerm}(W))\) |
| \(\operatorname{runCase}_{A,B}(V,W,M)\) | \(\operatorname{runCase}_{\operatorname{RfType}(A),\operatorname{RfType}(B)}(\operatorname{RfTerm}(V),\operatorname{RfTerm}(W),\operatorname{RfTerm}(M))\) |

- \(A\in\mathsf{Ty}_{*^v_i}\)
- \(M\in\mathsf{Tm}_{*^c_i}\)
- \(V\in\mathsf{Tm}_{*^v_i}\)
- \(N\in\mathsf{Tm}_{*^c_j}\)
- \(\operatorname{RfTerm}(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N) =(\lambda_{s^{i,j}}\bar x:\operatorname{RfType}(A).\operatorname{RfTerm}(N)) @_{s^{i,j}}\operatorname{RfTerm}(M)\)
- \(\operatorname{RfTerm}(\operatorname{let}^v x:A=V\ \operatorname{in}\ N) =(\lambda_{s^{i,j}}\bar x:\operatorname{RfType}(A).\operatorname{RfTerm}(N)) @_{s^{i,j}}\operatorname{RfTerm}(V)\)

#### Well-termination

- \(\Theta\vdash P:*^q_i\)
- \(\Delta\Vdash p:P\quad:\Longleftrightarrow\quad \Delta\vdash p:P\ \land\ \operatorname{RfCtx}(\Delta)\vdash\operatorname{RfTerm}(p):\operatorname{RfType}(P)\)

### Boxed Program

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| box type | \(\Gamma\vdash\operatorname{Box}(P):*^s_i\) | \(\operatorname{WF}(\Gamma)\)<br>\(\varnothing\vdash P:*^q_i\) | |
| box intro | \(\Gamma\vdash\operatorname{box}_P(p):\operatorname{Box}(P)\) | \(\operatorname{WF}(\Gamma)\)<br>\(\varnothing\vdash P:*^q_i\)<br>\(\varnothing\Vdash p:P\) | |
| force box | \(\Gamma\vdash\operatorname{Force}_P(b):\operatorname{RfType}(P)\) | \(\varnothing\vdash P:*^q_i\)<br>\(\Gamma\vdash b:\operatorname{Box}(P)\) | |
| boxed value application | \(\Gamma\vdash\operatorname{bapp}_{A,\underline B}(f,a):\operatorname{Box}(\underline B)\) | \(\varnothing\vdash A:*^v_i\)<br>\(\varnothing\vdash\underline B:*^c_j\)<br>\(\Gamma\vdash f:\operatorname{Box}(A\to_{r^{i,j}_{vc}}\underline B)\)<br>\(\Gamma\vdash a:\operatorname{Box}(A)\) | |
| boxed type application | \(\Gamma\vdash\operatorname{btapp}_{X:K,\underline B}(f,P):\operatorname{Box}(\underline B[X:=P])\) | \(\varnothing\vdash K:\square^q_i\)<br>\(X:K\vdash\underline B:*^c_j\)<br>\(\varnothing\vdash P:K\)<br>\(\Gamma\vdash f:\operatorname{Box}(\Pi_{r^{q;i,j}_{tc}}X:K.\underline B)\) | |

## 帰納型と CBPV

### 宣言

- \(\operatorname{inductive}\ I^v(X_1:K_1,\ldots,X_n:K_n):*^v_k\)
  - \(\operatorname{where}\ (C_h^v(x_1:A_{h1},\ldots,x_{m_h}:A_{hm_h}):I^v(\vec X))_{h=1}^{m}\)
- \(\Theta_0:=\varnothing\)
- \(\Theta_l:=\Theta_{l-1},X_l:K_l\)
- \(K_l\in\mathsf{Kd}_{*^{q_l}_{i_l}}\)
- \(A_{hj}\in\mathsf{Ty}_{*^v_{d_{hj}}}\)

\(\mathcal D\) は宣言環境とし、judgement の \(\mathcal D\) 添字を省略する。
\(\operatorname{StrictPos}(I,A)\) は \(A\) 内の \(I\) の全出現の strict positivity、
\(\operatorname{Expand}_{\mathrm{ty}}(A)\) は型演算子を展開した型とする。

| category | condition |
| --- | --- |
| parameter kind | \(\forall l\in\{1,\ldots,n\}.\ \Theta_{l-1}\vdash K_l:\square^{q_l}_{i_l}\ \land\ i_l\leq k\) |
| parameter scope | \(\forall l.\ \operatorname{FV}(K_l)\subseteq\{X_1,\ldots,X_{l-1}\}\) |
| field formation | \(\forall h,j.\ \Theta_n\vdash_{\mathcal D,I^v(\vec X:\vec K):*^v_k}A_{hj}:*^v_{d_{hj}}\ \land\ d_{hj}\leq k\) |
| field scope | \(\forall h,j.\ \operatorname{FV}(A_{hj})\subseteq\{X_1,\ldots,X_n\}\) |
| positivity | \(\forall h,j.\ \operatorname{StrictPos}(I^v,A_{hj})\ \land\ \operatorname{StrictPos}(I^s,\operatorname{Expand}_{\mathrm{ty}}(\operatorname{RfType}(A_{hj})))\) |
| fresh names | \(\{I^v,I^s,C_1^v,C_1^s,\ldots,C_m^v,C_m^s\}\cap\operatorname{names}(\mathcal D)=\varnothing\) |
| distinct names | \(\lvert\{I^v,I^s,C_1^v,C_1^s,\ldots,C_m^v,C_m^s\}\rvert=2m+2\) |
| distinct parameters | \(\lvert\{X_1,\ldots,X_n\}\rvert=n\) |

### Set の鏡像

- \(K_l^s:=\operatorname{RfKind}(K_l)\)
- \(A_{hj}^s:=\operatorname{RfType}(A_{hj})\)
- \(I^s(\bar X_1:K_1^s,\ldots,\bar X_n:K_n^s):*^s_k\)
- \(C_h^s(\bar x_1:A_{h1}^s,\ldots,\bar x_{m_h}:A_{hm_h}^s):I^s(\vec{\bar X})\)

### 構文

- \(P_l\in\mathsf{Ty}_{*^{q_l}_{i_l}}\)
- \(S_l\in\mathsf{Ty}_{*^s_{i_l}}\)
- \(V_{hj}\in\mathsf{Tm}_{*^v_{d_{hj}}}\)
- \(t_{hj}\in\mathsf{Tm}_{*^s_{d_{hj}}}\)
- \(V\in\mathsf{Tm}_{*^v_k}\)
- \(t\in\mathsf{Tm}_{*^s_k}\)
- \(\underline B\in\mathsf{Ty}_{*^c_j}\)
- \(B\in\mathsf{Ty}_{*^s_j}\)
- \(M_h\in\mathsf{Tm}_{*^c_j}\)
- \(u_h\in\mathsf{Tm}_{*^s_j}\)

| category | definition | family |
| --- | --- | --- |
| value type | \(I^v(\vec P)\) | \(\mathsf{Ty}_{*^v_k}\) |
| value | \(C_h^v[\vec P](\vec V_h)\) | \(\mathsf{Tm}_{*^v_k}\) |
| computation | \(\operatorname{case}^v_{\underline B}(V;(C_h^v(\vec x_h)\mapsto M_h)_{h=1}^{m})\) | \(\mathsf{Tm}_{*^c_j}\) |
| Set type | \(I^s(\vec S)\) | \(\mathsf{Ty}_{*^s_k}\) |
| Set term | \(C_h^s[\vec S](\vec t_h)\) | \(\mathsf{Tm}_{*^s_k}\) |
| Set case | \(\operatorname{case}^s_B(t;(C_h^s(\vec x_h)\mapsto u_h)_{h=1}^{m})\) | \(\mathsf{Tm}_{*^s_j}\) |

- \(\lvert\vec P\rvert=\lvert\vec S\rvert=n\)
- \(\lvert\vec V_h\rvert=\lvert\vec t_h\rvert=\lvert\vec x_h\rvert=m_h\)

### Program constructor と case

- \(\theta_l:=[X_a:=P_a]_{a=1}^{l}\)
- \(\theta_0:=[]\)
- \(\Theta\vdash\vec P:\vec K \;:\Longleftrightarrow\; \lvert\vec P\rvert=n\ \land\ \forall l\in\{1,\ldots,n\}.\ \Theta\vdash P_l:K_l\theta_{l-1}\)
- \(\Phi_h^v(\vec P):=(x_{h1}:A_{h1}\theta_n,\ldots,x_{hm_h}:A_{hm_h}\theta_n)\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| inductive type form | \(\Theta\vdash I^v(\vec P):*^v_k\) | \(\Theta\vdash\vec P:\vec K\) | \(I^v\in\mathcal D\) |
| constructor intro | \(\Delta\vdash C_h^v[\vec P](\vec V):I^v(\vec P)\) | \(\Theta\vdash\vec P:\vec K\)<br>\(\forall a\in\{1,\ldots,m_h\}.\ \Delta\vdash V_a:A_{ha}\theta_n\) | \(1\leq h\leq m\)<br>\(\lvert\vec V\rvert=m_h\) |
| case | \(\Delta\vdash\operatorname{case}^v_{\underline B}(V;(C_h^v(\vec x_h)\mapsto M_h)_{h=1}^{m}):\underline B\) | \(\Theta\vdash\vec P:\vec K\)<br>\(\Theta\vdash\underline B:*^c_j\)<br>\(\Delta\vdash V:I^v(\vec P)\)<br>\(\forall h\in\{1,\ldots,m\}.\ \Delta,\Phi_h^v(\vec P)\vdash M_h:\underline B\) | \(\forall h.\ \lvert\{\vec x_h\}\rvert=m_h\)<br>\(\forall h.\ \{\vec x_h\}\cap\operatorname{dom}(\Delta)=\varnothing\) |

### Set constructor と case

- \(\eta_l:=[\bar X_a:=S_a]_{a=1}^{l}\)
- \(\eta_0:=[]\)
- \(\Gamma\vdash\vec S:\vec K^s \;:\Longleftrightarrow\; \lvert\vec S\rvert=n\ \land\ \forall l\in\{1,\ldots,n\}.\ \Gamma\vdash S_l:K_l^s\eta_{l-1}\)
- \(\Phi_h^s(\vec S):=(x_{h1}:A_{h1}^s\eta_n,\ldots,x_{hm_h}:A_{hm_h}^s\eta_n)\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| inductive type form | \(\Gamma\vdash I^s(\vec S):*^s_k\) | \(\Gamma\vdash\vec S:\vec K^s\) | \(I^v\in\mathcal D\) |
| constructor intro | \(\Gamma\vdash C_h^s[\vec S](\vec t):I^s(\vec S)\) | \(\Gamma\vdash\vec S:\vec K^s\)<br>\(\forall a\in\{1,\ldots,m_h\}.\ \Gamma\vdash t_a:A_{ha}^s\eta_n\) | \(1\leq h\leq m\)<br>\(\lvert\vec t\rvert=m_h\) |
| case | \(\Gamma\vdash\operatorname{case}^s_B(t;(C_h^s(\vec x_h)\mapsto u_h)_{h=1}^{m}):B\) | \(\Gamma\vdash\vec S:\vec K^s\)<br>\(\Gamma\vdash B:*^s_j\)<br>\(\Gamma\vdash t:I^s(\vec S)\)<br>\(\forall h\in\{1,\ldots,m\}.\ \Gamma,\Phi_h^s(\vec S)\vdash u_h:B\) | \(\forall h.\ \lvert\{\vec x_h\}\rvert=m_h\)<br>\(\forall h.\ \{\vec x_h\}\cap(\operatorname{dom}(\Gamma)\cup\operatorname{FV}(B))=\varnothing\) |

### reduction

- \(\operatorname{case}^v_{\underline B} (C_h^v[\vec P](\vec V);(C_l^v(\vec x_l)\mapsto M_l)_{l=1}^{m}) \Rightarrow_{\mathsf{Tm}_{*^c_j}}M_h[\vec x_h:=\vec V]\)
- \(\operatorname{case}^s_B (C_h^s[\vec S](\vec t);(C_l^s(\vec x_l)\mapsto u_l)_{l=1}^{m}) \Rightarrow_{\mathsf{Tm}_{*^s_j}}u_h[\vec x_h:=\vec t]\)

### Reflection

- \(\operatorname{RfType}(I^v(\vec P)) :=I^s(\operatorname{RfType}(\vec P))\)
- \(\operatorname{RfTerm}(C_h^v[\vec P](\vec V)) :=C_h^s[\operatorname{RfType}(\vec P)](\operatorname{RfTerm}(\vec V))\)
- \(\operatorname{RfTerm}\left(\operatorname{case}^v_{\underline B} (V;(C_h^v(\vec x_h)\mapsto M_h)_{h=1}^{m})\right) :=\operatorname{case}^s_{\operatorname{RfType}(\underline B)} \left(\operatorname{RfTerm}(V); (C_h^s(\vec{\bar x}_h)\mapsto\operatorname{RfTerm}(M_h))_{h=1}^{m}\right)\)
