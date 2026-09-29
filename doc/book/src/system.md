# Core calculus
> [!note]
> この block quote は削除しないし追記しないでください。
> 
> `system.md` は体系を簡潔に述べるところです。
> 次のことをしないでください。
> 会話由来の「○○しない」を書かない
> 過去の状態から変更した理由を書かない
> 体系の性質/定理を書かない

## Sort

- \(\mathcal B:=\mathcal B_{sp}\cup\mathcal B_{pr}\)
  - \(\mathcal B_{sp}:=\{*^s_i\mid i\in\mathbb N\}\cup\{*^p\}\)
  - \(\mathcal B_{pr}:=\{*^v_i,*^c_i\mid i\in\mathbb N\}\)
- \(\mathcal K:=\mathcal K_{sp}\cup\mathcal K_{pr}\)
  - \(\mathcal K_{sp}:=\{\square^s_i\mid i\in\mathbb N\}\cup\{\square^p\}\)
  - \(\mathcal K_{pr}:=\{\square^v_i,\square^c_i\mid i\in\mathbb N\}\)
- \(\kappa:\mathcal B\to\mathcal K\)
  - \(\kappa(*^s_i):=\square^s_i\) for \(i \in \mathbb N\)
  - \(\kappa(*^p):=\square^p\)
  - \(\kappa(*^q_i):=\square^q_i\) for \(q\in\{v,c\}, i \in \mathbb N\)
- \(\mathcal S:=\mathcal B\cup\mathcal K\)
  - \(\mathcal S_{sp}:=\mathcal B_{sp}\cup\mathcal K_{sp}\)
  - \(\mathcal S_{pr}:=\mathcal B_{pr}\cup\mathcal K_{pr}\)
- \(\mathcal A:=\{(b,\kappa(b))\mid b\in\mathcal B\}\)

### 以降での添え字についての仮定

- \(i,j,k,h\in\mathbb N\)
- \(q,q'\in\{v,c\}\)
- \(b\in\mathcal B\)
- \(\sigma,\sigma_1,\sigma_2,\sigma_3\in\mathcal S\)

### Product signature

- \(\mathcal R_s:=\bigcup_{i,j\in\mathbb N}\{(*^s_i,*^s_j,*^s_{\max(i,j)}),(*^s_i,\square^s_j,\square^s_{\max(i,j)}),(\square^s_i,\square^s_j,\square^s_{\max(i,j)}),(\square^s_i,*^s_j,*^s_{\max(i+1,j)})\}\)
- \(\mathcal R_p:=\{(*^p,*^p,*^p),(\square^p,*^p,*^p),(\square^p,\square^p,\square^p)\}\cup\bigcup_{i\in\mathbb N}\{(\sigma,\tau,\tau)\mid\sigma\in\{*^s_i,\square^s_i\},\ \tau\in\{*^p,\square^p\}\}\)
- \(\mathcal R_{sp}:=\mathcal R_s\cup\mathcal R_p\)
- \(\mathcal R_{pr}:=\bigcup_{i,j\in\mathbb N}\{(*^v_i,*^c_j,*^c_{\max(i,j)})\}\cup\bigcup_{q\in\{v,c\},\ i,j\in\mathbb N}\{(\square^q_i,*^c_j,*^c_{\max(i+1,j)})\}\cup\bigcup_{q,q'\in\{v,c\},\ i,j\in\mathbb N}\{(\square^q_i,\square^{q'}_j,\square^{q'}_{\max(i,j)})\}\)
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

#### Syntax

可算無限の変数集合 \(\mathsf{Var}\) と、次の構成子から項の集合 \(\mathsf{Exp}\) を生成し、alpha 同値で同一視する。
\(e,A,B,K,P,V,M\) などは共通の項を表し、\(x,X,z\in\mathsf{Var}\) とする。
項の分類と各引数の条件は型判断で与える。
Set/Prop と Program で同じ記号を使う固有演算は、演算の tag で区別する。

#### Basic constructor

| category | definition |
| --- | --- |
| sort | \(\sigma\in\mathcal S\) |
| variable | \(z\) |
| dependent product | \(\Pi z:A.B\) |
| lambda abstraction | \(\lambda_m z:A.e\) |
| application | \(f@_m a\) |

\(m\in\{\mathsf{pure},\mathsf{computation}\}\) は評価の種類を指定する tag とする。
以下の \(\Pi_r\)、\(\lambda_r\)、\(@_r\) は、型判断で導出した \(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R\) を示す略記とする。
\(\Pi_r\) は \(\Pi\)、\(r\) の結果が Program computation の場合の \(\lambda_r\)・\(@_r\) は \(m=\mathsf{computation}\)、それ以外は \(m=\mathsf{pure}\) に対応する。

#### Set/Prop

| category | definition |
| --- | --- |
| power set | \(\Power A\) |
| type lift | \(\Ty(A,u)\) |
| refinement | \(\{x:A\mid P\}\) |
| predicate | \(\Pred(A,u,a)\) |
| equality | \(a=b\) |
| existence | \(\exists A\) |
| proof mark | \(\Proof P\) |
| take set | \(\Take^s_i(X,T,f)\) |
| take prop | \(\Take^p_i(X,P,g)\) |
| run step | \(\operatorname{RunStep}(A,B)\) |
| continue | \(\operatorname{continue}_{A,B}(a)\) |
| finish | \(\operatorname{finish}_{A,B}(b)\) |
| accessibility | \(\operatorname{Acc}_{A,B}(f,a)\) |
| run | \(\operatorname{run}_{A,B}(f,a)\) |
| run case | \(\operatorname{runCase}_{A,B}(f,a,u)\) |
| run step match | \(\operatorname{stepMatch}^{\sigma}_{A,B}(x.P,c,d)\) |

#### Program

| category | notation |
| --- | --- |
| value type constructor | \(A,B\) |
| computation type constructor | \(\underline B\) |
| value | \(V,W\) |
| computation | \(M,N\) |

| category | definition |
| --- | --- |
| returner type | \(F A\) |
| thunk type | \(U\underline C\) |
| run step type | \(\operatorname{RunStep}(A,B)\) |
| return | \(\operatorname{return}(V)\) |
| thunk | \(\operatorname{thunk}(M)\) |
| force | \(\operatorname{force}(V)\) |
| sequence | \(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N\) |
| value let | \(\operatorname{let}^v x:A=V\ \operatorname{in}\ N\) |
| continue | \(\operatorname{continue}_{A,B}(V)\) |
| finish | \(\operatorname{finish}_{A,B}(V)\) |
| run step match | \(\operatorname{stepMatch}_{A,B,\underline C}(M,N,V)\) |
| run | \(\operatorname{run}_{A,B}(V,W)\) |
| run case | \(\operatorname{runCase}_{A,B}(V,W,M)\) |

#### Boxed Computation

| category | definition |
| --- | --- |
| boxed computation type | \(\operatorname{Box}(\underline B)\) |
| boxed computation | \(\operatorname{box}_{\underline B}(M)\) |
| force boxed computation | \(\operatorname{Force}_{\underline B}(t)\) |
| boxed application | \(\operatorname{bapp}_{A,\underline C}(f,a)\) |
| boxed type application | \(\operatorname{btapp}_{X:K,\underline C}(f,P)\) |

#### Binder と substitution

| constructor | bound variable | scope |
| --- | --- | --- |
| \(\Pi_r z:A.B\) | \(z\) | \(B\) |
| \(\lambda_r z:A.e\) | \(z\) | \(e\) |
| \(\{x:A\mid P\}\) | \(x\) | \(P\) |
| \(\operatorname{stepMatch}^{\sigma}_{A,B}(x.P,c,d)\) | \(x\) | \(P\) |
| \(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N\) | \(x\) | \(N\) |
| \(\operatorname{let}^v x:A=V\ \operatorname{in}\ N\) | \(x\) | \(N\) |
| \(\operatorname{btapp}_{X:K,\underline B}(f,P)\) | \(X\) | \(\underline B\) |
| \(\operatorname{case}^d_B(t;\overline{C_l^d(\vec x_l)\mapsto e_l})\) | \(\vec x_l\) | \(e_l\) |

\(e[z:=a]\) は項の全構成子・binder の型・型引数を辿る capture-avoiding substitution とする。

### Context と judgement

- \(H::=\varnothing\mid H,z:A\)
- \(\Gamma\) は Set/Prop の仮定を持つ文脈、\(\Delta\) は Program の型変数・値変数を持つ文脈とする。
- \(\Theta:=\operatorname{TyCtx}(\Delta)\) は、\(\Delta\) の型変数の宣言を順序を保って取り出した文脈とする。
- \(\operatorname{TyCtx}(\varnothing):=\varnothing\)
- \(\operatorname{TyCtx}(\Delta,X:K):=\operatorname{TyCtx}(\Delta),X:K\quad(\Theta\vdash K:\square^q_i)\)
- \(\operatorname{TyCtx}(\Delta,x:A):=\operatorname{TyCtx}(\Delta)\quad(\Theta\vdash A:*^v_i)\)

| category | judgement |
| --- | --- |
| well formed context | \(\operatorname{WF}(H)\) |
| typing | \(H\vdash e:A\) |
| provable | \(\Gamma\vDash P\) |

Program の型・kind の形成は \(\Theta\) の下で判断する。
Set/Prop の文脈拡張には \(\mathcal S_{sp}\)、Program の文脈拡張には \(\{*^v_i,\square^v_i,\square^c_i\mid i\in\mathbb N\}\) に属する sort を用いる。

## reduction

### Compatible closure

\(\Rightarrow\;\subseteq\;\mathsf{Exp}\times\mathsf{Exp}\) は以下の root・閉包規則と帰納型の case 規則で生成される最小の関係とする。
\(C\) は、次の位置に穴を持つ一穴構文文脈とする。
以下の reduction の表の各行は \(\mathrm{before}\Rightarrow\mathrm{after}\) を表す。

| expression | compatible position |
| --- | --- |
| Set/Prop の項 | 全 Set/Prop 引数（binder の型・body を含む） |
| Program の型・kind | 全 Program 型・kind 引数（binder の型・body を含む） |

| category | before | after | premise |
| --- | --- | --- | --- |
| compatible closure | \(C[e]\) | \(C[e']\) | \(e\Rightarrow e'\) |

### Basic beta

| category | before | after | premise |
| --- | --- | --- | --- |
| beta | \((\lambda_r z:A.e)@_r a\) | \(e[z:=a]\) | \(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R\)<br>\(r\in\mathcal R_{sp}\ \lor\ \sigma_2\in\kappa(\mathcal B_{pr})\) |

### Set/Prop

| category | before | after | premise |
| --- | --- | --- | --- |
| predicate | \(\Pred(A,\{x:B\mid P\},t)\) | \((\lambda_{p_i}x:B.P)@_{p_i}t\) | |
| step match continue | \(\operatorname{stepMatch}^{\sigma}_{A,B}(x.P,c,d)@_{h_{i,\sigma}}\operatorname{continue}_{A,B}(a)\) | \(c@_{h_{i,\sigma}}a\) | |
| step match finish | \(\operatorname{stepMatch}^{\sigma}_{A,B}(x.P,c,d)@_{h_{i,\sigma}}\operatorname{finish}_{A,B}(b)\) | \(d@_{h_{i,\sigma}}b\) | |
| run | \(\operatorname{run}_{A,B}(f,a)\) | \(\operatorname{runCase}_{A,B}(f,a,f@_{s^{i,i}}a)\) | |
| run continue | \(\operatorname{runCase}_{A,B}(f,a,\operatorname{continue}_{A,B}(a'))\) | \(\operatorname{run}_{A,B}(f,a')\) | |
| run finish | \(\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{A,B}(b))\) | \(b\) | |

### Program

Program の computation の簡約は、次の evaluation context と root 規則で生成する。

#### Evaluation context

\[
E::=[\,]\mid E@_{r^{i,j}_{vc}}V\mid E@_{r^{q;i,j}_{tc}}P
\mid E\ \operatorname{to}\ x:A\ \operatorname{in}\ N
\mid\operatorname{runCase}_{A,B}(V,W,E).
\]

各 context の型は Program の型判断に従い、\(V,W\) は値、\(P\) は型引数とする。

| category | before | after | premise |
| --- | --- | --- | --- |
| evaluation context | \(E[M]\) | \(E[M']\) | \(M\Rightarrow M'\) |

#### Computation root

| category | before | after | premise |
| --- | --- | --- | --- |
| force thunk | \(\operatorname{force}(\operatorname{thunk}(M))\) | \(M\) | |
| value beta | \((\lambda_{r^{i,j}_{vc}}x:A.M)@_{r^{i,j}_{vc}}V\) | \(M[x:=V]\) | |
| type beta | \((\lambda_{r^{q;i,j}_{tc}}X:K.M)@_{r^{q;i,j}_{tc}}P\) | \(M[X:=P]\) | |
| sequence | \(\operatorname{return}(V)\ \operatorname{to}\ x:A\ \operatorname{in}\ N\) | \(N[x:=V]\) | |
| value let | \(\operatorname{let}^v x:A=V\ \operatorname{in}\ N\) | \(N[x:=V]\) | |
| step match continue | \(\operatorname{stepMatch}_{A,B,\underline C}(M,N,\operatorname{continue}_{A,B}(V))\) | \(M@_{r^{i,j}_{vc}}V\) | \(M:A\to_{r^{i,j}_{vc}}\underline C\) |
| step match finish | \(\operatorname{stepMatch}_{A,B,\underline C}(M,N,\operatorname{finish}_{A,B}(V))\) | \(N@_{r^{i,j}_{vc}}V\) | \(N:B\to_{r^{i,j}_{vc}}\underline C\) |
| run | \(\operatorname{run}_{A,B}(f,a)\) | \(\operatorname{runCase}_{A,B}(f,a,\operatorname{force}(f)@_{r^{i,i}_{vc}}a)\) | |
| run continue | \(\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a')))\) | \(\operatorname{run}_{A,B}(f,a')\) | |
| run finish | \(\operatorname{runCase}_{A,B}(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b)))\) | \(\operatorname{return}(b)\) | |

### Boxed Computation

| category | before | after | premise |
| --- | --- | --- | --- |
| box step | \(\operatorname{box}_{\underline B}(M)\) | \(\operatorname{box}_{\underline B}(M')\) | \(M\Rightarrow M'\) |
| force box | \(\operatorname{Force}_{\underline B}(\operatorname{box}_{\underline B}(M))\) | \(\operatorname{Rf}(M)\) | \(\varnothing\vdash\underline B:*^c_i\)<br>\(\varnothing\vdash M:\underline B\)<br>\(\nexists M'.\ M\Rightarrow M'\) |
| boxed application | \(\operatorname{bapp}_{A,\underline B}(\operatorname{box}_{A\to_{r^{i,j}_{vc}}\underline B}(M),\operatorname{box}_{F A}(\operatorname{return}(V)))\) | \(\operatorname{box}_{\underline B}(M@_{r^{i,j}_{vc}}V)\) | |
| boxed type application | \(\operatorname{btapp}_{X:K,\underline B}(\operatorname{box}_{\Pi_{r^{q;i,j}_{tc}}X:K.\underline B}(M),P)\) | \(\operatorname{box}_{\underline B[X:=P]}(M@_{r^{q;i,j}_{tc}}P)\) | |

### definitional equality

- \(\equiv:=(\Rightarrow\cup\Leftarrow)^*\)

## derivation

### Context と basic typing

typing・provability 規則は、出現する context の \(\operatorname{WF}\) を前提とする。
導出は有限木とする。

- \(H::e:=H,e\)
- \(r=(\sigma_1,\sigma_2,\sigma_3)\in\mathcal R\)
- \(d\in\{sp,pr\}\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| empty | \(\operatorname{WF}(\varnothing)\) | | |
| axiom | \(H\vdash b:\kappa(b)\) | \(\operatorname{WF}(H)\) | \((b,\kappa(b))\in\mathcal A\) |
| start | \(\operatorname{WF}(H,z:A)\) | \(\operatorname{WF}(H)\)<br>\(H\vdash A:\sigma\) | \(z\notin\operatorname{dom}(H)\)<br>\(\sigma\) は文脈に対応する sort |
| variable | \(H,z:A\vdash z:A\) | \(\operatorname{WF}(H,z:A)\) | |
| weak | \(H,z:A\vdash J\) | \(H\vdash J\)<br>\(\operatorname{WF}(H,z:A)\) | \(z\notin\operatorname{FV}(J)\) |
| provable weak | \(\Gamma,z:A\vDash P\) | \(\Gamma\vDash P\)<br>\(\operatorname{WF}(\Gamma,z:A)\) | \(z\notin\operatorname{FV}(P)\) |
| conversion | \(H\vdash e:B\) | \(H\vdash e:A\)<br>\(H\vdash A:\sigma\)<br>\(H\vdash B:\sigma\) | \(A\equiv B\) |
| dep form | \(H\vdash\Pi_r z:A.B:\sigma_3\) | \(H\vdash A:\sigma_1\)<br>\(H,z:A\vdash B:\sigma_2\) | \(z\notin\operatorname{dom}(H)\)<br>\(r=r^{i,j}_{vc}\Longrightarrow z\notin\operatorname{FV}(B)\) |
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
| subset form | \(\Gamma\vdash\{x:A\mid P\}:\Power A\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma,x:A\vdash P:*^p\) | \(x\notin\operatorname{dom}(\Gamma)\) |
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
| step match | \(\Gamma\vdash\operatorname{stepMatch}^{\sigma}_{A,B}(x.P,c,d):\Pi_{h_{i,\sigma}}x:D.P\) | \(\Gamma\vdash A:*^s_i\)<br>\(\Gamma\vdash B:*^s_i\)<br>\(\Gamma,x:D\vdash P:\sigma\)<br>\(\Gamma\vdash C_P:\tau\)<br>\(\Gamma\vdash D_P:\tau\)<br>\(\Gamma\vdash c:C_P\)<br>\(\Gamma\vdash d:D_P\) | \(\{x,a,b\}\cap\operatorname{dom}(\Gamma)=\varnothing\)<br>\(\lvert\{x,a,b\}\rvert=3\) |

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
| step match | \(\Delta\vdash\operatorname{stepMatch}_{A,B,\underline C}(M,N,V):\underline C\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Theta\vdash\underline C:*^c_j\)<br>\(\Delta\vdash M:A\to_{r^{i,j}_{vc}}\underline C\)<br>\(\Delta\vdash N:B\to_{r^{i,j}_{vc}}\underline C\)<br>\(\Delta\vdash V:\operatorname{RunStep}(A,B)\) | |
| run | \(\Delta\vdash\operatorname{run}_{A,B}(f,a):F B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Delta\vdash f:T_{A,B}\)<br>\(\Delta\vdash a:A\) | |
| run case | \(\Delta\vdash\operatorname{runCase}_{A,B}(f,a,M):F B\) | \(\Theta\vdash A:*^v_i\)<br>\(\Theta\vdash B:*^v_i\)<br>\(\Delta\vdash f:T_{A,B}\)<br>\(\Delta\vdash a:A\)<br>\(\Delta\vdash M:F(\operatorname{RunStep}(A,B))\) | |

#### Polymorphism

- \(k:=\max(i+1,j)\)
- \(r:=r^{q;i,j}_{tc}\)

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| type product | \(\Theta\vdash\Pi_r X:K.\underline B:*^c_k\) | \(\Theta\vdash K:\square^q_i\)<br>\(\Theta,X:K\vdash\underline B:*^c_j\) | \(X\notin\operatorname{dom}(\Theta)\) |
| type abstraction | \(\Delta\vdash\lambda_r X:K.M:\Pi_r X:K.\underline B\) | \(\Theta\vdash K:\square^q_i\)<br>\(\Theta,X:K\vdash\underline B:*^c_j\)<br>\(\Theta\vdash\Pi_r X:K.\underline B:*^c_k\)<br>\(\Delta,X:K\vdash M:\underline B\) | \(X\notin\operatorname{dom}(\Delta)\) |
| type application | \(\Delta\vdash M@_r P:\underline B[X:=P]\) | \(\Theta\vdash K:\square^q_i\)<br>\(\Theta,X:K\vdash\underline B:*^c_j\)<br>\(\Delta\vdash M:\Pi_r X:K.\underline B\)<br>\(\Theta\vdash P:K\) | \(X\notin\operatorname{dom}(\Delta)\) |

#### Reflection

##### Meta-level maps

名前の反映 \(z\mapsto\bar z\) は単射とする。
reflection は Program の型判断で分類された項に対し、以下の式で定義する。

- \(\overline{*^q_i}:=*^s_i\)
- \(\overline{\square^q_i}:=\square^s_i\)
- \(\overline{(\sigma_1,\sigma_2,\sigma_3)}:=(\bar\sigma_1,\bar\sigma_2,\bar\sigma_3)\)

##### Basic constructor と context

- \(\operatorname{Rf}(z):=\bar z\)
- \(\operatorname{Rf}(*^q_i):=*^s_i\)
- \(\operatorname{Rf}(\square^q_i):=\square^s_i\)
- \(\operatorname{Rf}(\Pi_r z:A.B):=\Pi_{\bar r}\bar z:\operatorname{Rf}(A).\operatorname{Rf}(B)\)
- \(\operatorname{Rf}(\lambda_r z:A.e):=\lambda_{\bar r}\bar z:\operatorname{Rf}(A).\operatorname{Rf}(e)\)
- \(\operatorname{Rf}(f@_r a):=\operatorname{Rf}(f)@_{\bar r}\operatorname{Rf}(a)\)
- \(\operatorname{RfCtx}(\varnothing):=\varnothing\)
- \(\operatorname{RfCtx}(\Delta,X:K):=\operatorname{RfCtx}(\Delta),\bar X:\operatorname{Rf}(K)\)
- \(\operatorname{RfCtx}(\Delta,x:A):=\operatorname{RfCtx}(\Delta),\bar x:\operatorname{Rf}(A)\)

##### Program constructor

| constructor | reflection |
| --- | --- |
| \(F A\) | \(\operatorname{Rf}(A)\) |
| \(U\underline B\) | \(\operatorname{Rf}(\underline B)\) |
| \(\operatorname{return}(V)\) | \(\operatorname{Rf}(V)\) |
| \(\operatorname{thunk}(M)\) | \(\operatorname{Rf}(M)\) |
| \(\operatorname{force}(V)\) | \(\operatorname{Rf}(V)\) |
| \(\operatorname{RunStep}(A,B)\) | \(\operatorname{RunStep}(\operatorname{Rf}(A),\operatorname{Rf}(B))\) |
| \(\operatorname{continue}_{A,B}(V)\) | \(\operatorname{continue}_{\operatorname{Rf}(A),\operatorname{Rf}(B)}(\operatorname{Rf}(V))\) |
| \(\operatorname{finish}_{A,B}(V)\) | \(\operatorname{finish}_{\operatorname{Rf}(A),\operatorname{Rf}(B)}(\operatorname{Rf}(V))\) |
| \(\operatorname{stepMatch}_{A,B,\underline C}(M,N,V)\) | \(\operatorname{stepMatch}^{\sigma}_{\operatorname{Rf}(A),\operatorname{Rf}(B)}(x.\operatorname{Rf}(\underline C),\operatorname{Rf}(M),\operatorname{Rf}(N))@_{h_{i,\sigma}}\operatorname{Rf}(V)\) |
| \(\operatorname{run}_{A,B}(V,W)\) | \(\operatorname{run}_{\operatorname{Rf}(A),\operatorname{Rf}(B)}(\operatorname{Rf}(V),\operatorname{Rf}(W))\) |
| \(\operatorname{runCase}_{A,B}(V,W,M)\) | \(\operatorname{runCase}_{\operatorname{Rf}(A),\operatorname{Rf}(B)}(\operatorname{Rf}(V),\operatorname{Rf}(W),\operatorname{Rf}(M))\) |

- \(\operatorname{Rf}(M\ \operatorname{to}\ x:A\ \operatorname{in}\ N):=(\lambda_{s^{i,j}}\bar x:\operatorname{Rf}(A).\operatorname{Rf}(N)) @_{s^{i,j}}\operatorname{Rf}(M)\)
- \(\operatorname{Rf}(\operatorname{let}^v x:A=V\ \operatorname{in}\ N):=(\lambda_{s^{i,j}}\bar x:\operatorname{Rf}(A).\operatorname{Rf}(N)) @_{s^{i,j}}\operatorname{Rf}(V)\)

### Boxed Computation

| category | conclusion | premises | other |
| --- | --- | --- | --- |
| box type | \(\Gamma\vdash\operatorname{Box}(\underline B):*^s_i\) | \(\operatorname{WF}(\Gamma)\)<br>\(\varnothing\vdash\underline B:*^c_i\) | |
| box intro | \(\Gamma\vdash\operatorname{box}_{\underline B}(M):\operatorname{Box}(\underline B)\) | \(\operatorname{WF}(\Gamma)\)<br>\(\varnothing\vdash\underline B:*^c_i\)<br>\(\varnothing\vdash M:\underline B\)<br>\(\varnothing\vdash\operatorname{Rf}(M):\operatorname{Rf}(\underline B)\) | |
| force box | \(\Gamma\vdash\operatorname{Force}_{\underline B}(b):\operatorname{Rf}(\underline B)\) | \(\varnothing\vdash\underline B:*^c_i\)<br>\(\Gamma\vdash b:\operatorname{Box}(\underline B)\) | |
| boxed application | \(\Gamma\vdash\operatorname{bapp}_{A,\underline B}(f,a):\operatorname{Box}(\underline B)\) | \(\varnothing\vdash A:*^v_i\)<br>\(\varnothing\vdash\underline B:*^c_j\)<br>\(\Gamma\vdash f:\operatorname{Box}(A\to_{r^{i,j}_{vc}}\underline B)\)<br>\(\Gamma\vdash a:\operatorname{Box}(F A)\) | |
| boxed type application | \(\Gamma\vdash\operatorname{btapp}_{X:K,\underline B}(f,P):\operatorname{Box}(\underline B[X:=P])\) | \(\varnothing\vdash K:\square^q_i\)<br>\(X:K\vdash\underline B:*^c_j\)<br>\(\varnothing\vdash P:K\)<br>\(\Gamma\vdash f:\operatorname{Box}(\Pi_{r^{q;i,j}_{tc}}X:K.\underline B)\) | |

## 帰納型と CBPV

### 宣言

- \(\operatorname{inductive}\ I^v(X_1:K_1,\ldots,X_n:K_n):*^v_k\)
  - \(\operatorname{where}\ (C_h^v(x_1:A_{h1},\ldots,x_{m_h}:A_{hm_h}):I^v(\vec X))_{h=1}^{m}\)
- \(\Theta_0:=\varnothing\)
- \(\Theta_l:=\Theta_{l-1},X_l:K_l\)

\(\mathcal D\) は宣言環境とし、judgement の \(\mathcal D\) 添字を省略する。
\(\operatorname{StrictPos}(I,A)\) は \(A\) 内の \(I\) の全出現の strict positivity、
\(\operatorname{Expand}_{\mathrm{ty}}(A)\) は型演算子を展開した型とする。

| category | condition |
| --- | --- |
| parameter kind | \(\forall l\in\{1,\ldots,n\}.\ \Theta_{l-1}\vdash K_l:\square^{q_l}_{i_l}\ \land\ i_l\leq k\) |
| parameter scope | \(\forall l.\ \operatorname{FV}(K_l)\subseteq\{X_1,\ldots,X_{l-1}\}\) |
| field formation | \(\forall h,j.\ \Theta_n\vdash_{\mathcal D,I^v(\vec X:\vec K):*^v_k}A_{hj}:*^v_{d_{hj}}\ \land\ d_{hj}\leq k\) |
| field scope | \(\forall h,j.\ \operatorname{FV}(A_{hj})\subseteq\{X_1,\ldots,X_n\}\) |
| positivity | \(\forall h,j.\ \operatorname{StrictPos}(I^v,A_{hj})\ \land\ \operatorname{StrictPos}(I^s,\operatorname{Expand}_{\mathrm{ty}}(\operatorname{Rf}(A_{hj})))\) |
| fresh names | \(\{I^v,I^s,C_1^v,C_1^s,\ldots,C_m^v,C_m^s\}\cap\operatorname{names}(\mathcal D)=\varnothing\) |
| distinct names | \(\lvert\{I^v,I^s,C_1^v,C_1^s,\ldots,C_m^v,C_m^s\}\rvert=2m+2\) |
| distinct parameters | \(\lvert\{X_1,\ldots,X_n\}\rvert=n\) |

### Set の鏡像

- \(K_l^s:=\operatorname{Rf}(K_l)\)
- \(A_{hj}^s:=\operatorname{Rf}(A_{hj})\)
- \(I^s(\bar X_1:K_1^s,\ldots,\bar X_n:K_n^s):*^s_k\)
- \(C_h^s(\bar x_1:A_{h1}^s,\ldots,\bar x_{m_h}:A_{hm_h}^s):I^s(\vec{\bar X})\)

### 構文

| category | definition |
| --- | --- |
| value type | \(I^v(\vec P)\) |
| value | \(C_h^v[\vec P](\vec V_h)\) |
| computation | \(\operatorname{case}^v_{\underline B}(V;(C_h^v(\vec x_h)\mapsto M_h)_{h=1}^{m})\) |
| Set type | \(I^s(\vec S)\) |
| Set term | \(C_h^s[\vec S](\vec t_h)\) |
| Set case | \(\operatorname{case}^s_B(t;(C_h^s(\vec x_h)\mapsto u_h)_{h=1}^{m})\) |

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

| category | before | after | premise |
| --- | --- | --- | --- |
| Program case | \(\operatorname{case}^v_{\underline B} (C_h^v[\vec P](\vec V);(C_l^v(\vec x_l)\mapsto M_l)_{l=1}^{m})\) | \(M_h[\vec x_h:=\vec V]\) | |
| Set case | \(\operatorname{case}^s_B (C_h^s[\vec S](\vec t);(C_l^s(\vec x_l)\mapsto u_l)_{l=1}^{m})\) | \(u_h[\vec x_h:=\vec t]\) | |

### Reflection

- \(\operatorname{Rf}(I^v(\vec P)) :=I^s(\operatorname{Rf}(\vec P))\)
- \(\operatorname{Rf}(C_h^v[\vec P](\vec V)) :=C_h^s[\operatorname{Rf}(\vec P)](\operatorname{Rf}(\vec V))\)
- \(\operatorname{Rf}\left(\operatorname{case}^v_{\underline B} (V;(C_h^v(\vec x_h)\mapsto M_h)_{h=1}^{m})\right) :=\operatorname{case}^s_{\operatorname{Rf}(\underline B)} \left(\operatorname{Rf}(V); (C_h^s(\vec{\bar x}_h)\mapsto\operatorname{Rf}(M_h))_{h=1}^{m}\right)\)
