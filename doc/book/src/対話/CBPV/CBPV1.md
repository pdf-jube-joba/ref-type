# Compute sort の CBPV 化 1

## 体系定義

### 構文定義

#### Sort

`system.md` の Set/Prop 側を \(D\) と呼び、その規則は変更しない。Compute 側の
proper sort も従来どおり \(*^c\) 一つとする。

\[
\begin{aligned}
\mathcal S
&=
\{*^s_i,\sq^s_i\mid i\in\mathbb N\}
\cup\{*^p,\sq^p\}
\cup\{*^c,\sq^c\},\\
\mathcal A
&=
\{(*^s_i,\sq^s_i)\mid i\in\mathbb N\}
\cup\{(*^p,\sq^p),(*^c,\sq^c)\},\\
\mathcal R
&=\mathcal R_{s,p}.
\end{aligned}
\]

ここで \(\mathcal R_{s,p}\) は `system.md` の Set/Prop に関する product relation である。
従来の \((*^c,*^c,*^c)\) は \(\mathcal R\) から外す。これを残すと、PTS の lambda/application
が後述の value/computation の区別を経由せずに形成できるためである。

計算の型と計算結果の値の型は、どちらも \(*^c\) に属する。Computation 自体を
分類する \(*^{cv}\), \(*^{cc}\) のような新しい sort は追加せず、value と computation は
term judgement で区別する。標準的な CBPV との対応は次の略記に埋め込む。

\[
\begin{aligned}
\Gamma\vdash_c M:A
&\quad\text{corresponds to}\quad
\Gamma\vdash M:F A,\\
A\Rightarrow B
&\quad\text{corresponds to}\quad
U(A\to F B).
\end{aligned}
\]

従って \(F\) と \(U\) は surface type constructor としては現れない。ここでの
\(A\Rightarrow B\) は「値 \(A\) を受け取り、値 \(B\) を返す computation を開始する
closure の型」である。

#### Context

context の形は `system.md` と同じである。

\[
\Gamma::=\emptyset\mid\Gamma,x:T:s.
\]

\(x:A:*^c\) は compute value variable の binding である。Computation variable は置かない。
bind は computation を実行した後、その結果を value variable として context に追加する。

#### Compute type

Compute type の基本形に非依存な value arrow と `RunStep` を追加する。

\[
A,B::=\cdots\mid A\Rightarrow B\mid\operatorname{RunStep}(A,B).
\]

\(A\Rightarrow B\) の codomain は binder に依存しない。Compute 側の dependent function はこの段階では
導入しない。

#### Compute value

\[
\begin{aligned}
V,W::={}&x^{*^c}
\mid\lambda^v x^{*^c}:A.M\\
&\mid c(V_1,\ldots,V_n)\\
&\mid\operatorname{continue}_{A,B}(V)
\mid\operatorname{finish}_{A,B}(V).
\end{aligned}
\]

\(c\) は Compute 側の datatype constructor を表す。Lambda の body は value ではなく
computation である。Lambda そのものは実行可能な closure であり value とする。

value の内部で reduction は進めない。特に lambda body と constructor argument の下は
compute reduction の compatible closure に含めない。Constructor argument は構文上すでに
value である。

#### Compute computation

\[
\begin{aligned}
M,N::={}&\operatorname{return}(V)\\
&\mid V\mathbin{@^c}W\\
&\mid\operatorname{bind}(M,x^{*^c}.N)\\
&\mid\operatorname{case}(V;\overline{c(\bar x)\mapsto M})\\
&\mid\operatorname{run}_{A,B}(f,a)\\
&\mid\operatorname{runStep}_{A,B}(f,a,M).
\end{aligned}
\]

\(\operatorname{runStep}\) は reduction 中にだけ現れる administrative term である。Surface term
として入力するものは \(\operatorname{run}\) である。型注釈と停止証明は raw term の一部として
保持してよいが、上の表記では省略する。

略記として次を使う。

\[
\operatorname{let}\ x\leftarrow M;N
:=
\operatorname{bind}(M,x.N).
\]

#### Value reflection

reflection の source は compute value に限定する。

\[
\operatorname{RfType}(A),
\qquad
\operatorname{RfVal}_A(V).
\]

\(\operatorname{RfVal}\) は従来の \(\operatorname{RfTerm}\) を value-only にしたものである。
名前を \(\operatorname{RfTerm}\) のまま残す実装も可能だが、ここでは source category が
判別できる名前を使う。

function value の reflection は extensional な Set function ではなく、closure/code の reflection
とする。従って、次の reduction は持たない。

\[
\operatorname{RfVal}_{A\Rightarrow B}(f)
@\operatorname{RfVal}_A(a)
\not\Rightarrow
\operatorname{RfVal}_B(f\mathbin{@^c}a).
\]

右辺の \(f\mathbin{@^c}a\) は value ではなく computation なので、\(\operatorname{RfVal}\) の
argument にはできない。

#### Application graph

function value の振る舞いは、Set 側の extensional function ではなく Prop 側の graph で記述する。

\[
\operatorname{AppEval}_{A,B}(g,a,b).
\]

これは、reflected closure \(g\) を reflected input \(a\) に適用する computation が
reflected value \(b\) を返すことを表す命題である。

`RunStep` の value constructor には Set 側の structural reflection を用意する。

\[
\begin{aligned}
\widehat{\operatorname{continue}}_{A,B}
&:\operatorname{RfType}(A)
\to\operatorname{RfType}(\operatorname{RunStep}(A,B)),\\
\widehat{\operatorname{finish}}_{A,B}
&:\operatorname{RfType}(B)
\to\operatorname{RfType}(\operatorname{RunStep}(A,B)).
\end{aligned}
\]

次の状態へ進む graph を略記する。

\[
\begin{aligned}
\operatorname{Next}_{A,B}(g,a,a')
:={}&
\operatorname{AppEval}_{A,\operatorname{RunStep}(A,B)}
\left(
g,
a,
\widehat{\operatorname{continue}}_{A,B}(a')
\right).
\end{aligned}
\]

#### Accessibility

\[
\begin{aligned}
\operatorname{Acc}_{A,B}(g,a)&:*^p,\\
\operatorname{Terminates}_{A,B}(f,a)
&:=
\operatorname{Acc}_{A,B}
\left(
\operatorname{RfVal}_{A\Rightarrow\operatorname{RunStep}(A,B)}(f),
\operatorname{RfVal}_A(a)
\right).
\end{aligned}
\]

\(\operatorname{Acc}\) は reflected application graph の \(\operatorname{Next}\) 辺に関する accessibility
である。これにより、Prop 側は computation そのものではなく、value の reflection
とその振る舞いを表す graph を参照する。

### Reduction 定義

#### Compute evaluation context

Compute reduction \(\Rightarrow_c\) は弱い call-by-value reduction とする。通常の全上下文の
compatible closure は使わず、次の evaluation context だけを使う。

\[
E::=[]
\mid\operatorname{bind}(E,x.M)
\mid\operatorname{runStep}_{A,B}(f,a,E).
\]

\[
\frac{M\Rightarrow_c M'}{E[M]\Rightarrow_c E[M']}.
\]

\(\operatorname{return}(V)\) の \(V\) の下、lambda body、constructor argument、および
未選択の case branch の下では reduction しない。

#### CBPV root rule

\[
\begin{aligned}
(\lambda^v x:A.M)\mathbin{@^c}V
&\Rightarrow_c M[x:=V],\\
\operatorname{bind}(\operatorname{return}(V),x.M)
&\Rightarrow_c M[x:=V],\\
\operatorname{case}
\left(c_i(\bar V);\overline{c_j(\bar x_j)\mapsto M_j}\right)
&\Rightarrow_c M_i[\bar x_i:=\bar V].
\end{aligned}
\]

置換される argument は常に value である。これにより、計算順序は構文と
evaluation context から一意に決まる。

#### General recursion

\[
\begin{aligned}
\operatorname{run}_{A,B}(f,a)
&\Rightarrow_c
\operatorname{runStep}_{A,B}
\left(f,a,f\mathbin{@^c}a\right),\\
\operatorname{runStep}_{A,B}
\left(f,a,\operatorname{return}(\operatorname{continue}_{A,B}(a'))\right)
&\Rightarrow_c
\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runStep}_{A,B}
\left(f,a,\operatorname{return}(\operatorname{finish}_{A,B}(b))\right)
&\Rightarrow_c
\operatorname{return}(b).
\end{aligned}
\]

\(\operatorname{runStep}\) の第三 argument だけが evaluation context に入る。従って一回の
step computation が value を返すまで、外側の再帰は進まない。

二つ目の規則で必要になる \(\operatorname{Terminates}_{A,B}(f,a')\) は、元の accessibility
証明と、第三 argument の評価履歴から得られる \(\operatorname{Next}\) の証明に
\(\operatorname{accDescent}\) を適用して構成する。証明 annotation は runtime では消去する。

#### Reflection

Compute reduction は \(\operatorname{RfVal}\) の下に入らない。Value constructor の structural
reflection だけに root rule を与える。

\[
\begin{aligned}
\operatorname{RfVal}_{\operatorname{RunStep}(A,B)}
\left(\operatorname{continue}_{A,B}(V)\right)
&\Rightarrow
\widehat{\operatorname{continue}}_{A,B}
\left(\operatorname{RfVal}_A(V)\right),\\
\operatorname{RfVal}_{\operatorname{RunStep}(A,B)}
\left(\operatorname{finish}_{A,B}(V)\right)
&\Rightarrow
\widehat{\operatorname{finish}}_{A,B}
\left(\operatorname{RfVal}_B(V)\right).
\end{aligned}
\]

一般の datatype constructor にも同様の structural reflection rule を生成する。Function value
は closure/code として保持し、その body を Set 項へ展開しない。

#### Definitional equality

Set/Prop 側の definitional equality \(\equiv_D\) は `system.md` のものを使う。Compute 側では
実行関係 \(\Rightarrow_c\) とその反射的推移閉包 \(\Rightarrow_c^*\) を区別して使う。
型注釈の conversion に使う static な型同値性を \(\equiv_{\mathrm{ty}}\) と書く。
これは Compute datatype/type constructor の型レベルの reduction と
\(\equiv_D\) が許す conversion を含むが、\(\Rightarrow_c\) による computation の実行は
含まない。

\(\Rightarrow_c\) を \(\equiv_D\) の compatible closure に追加しない。特に、computation を
Set 項の中で正規化することはできない。

### Judgement 定義

体系は次の judgement を持つ。

\[
\begin{array}{ll}
\operatorname{WF}(\Gamma)
&\text{well-formed context},\\
\Gamma\vdash_D t:T:s
&\text{Set/Prop typing},\\
\Gamma\vDash P
&\text{provability},\\
\Gamma\vdash A:*^c
&\text{compute value-type formation},\\
\Gamma\vdash_v V:A
&\text{compute value typing},\\
\Gamma\vdash_c M:A
&\text{compute computation returning an }A\text{ value}.
\end{array}
\]

\(\Gamma\vdash_c M:A\) は、\(M\) がすでに \(A\) の value であるという意味ではない。
実行すると \(\operatorname{return}(V)\) の形に到達し、\(\Gamma\vdash_v V:A\) となることを
意図した judgement である。

#### Compute type formation

| category | conclusion | premises |
| --- | --- | --- |
| value arrow form | \(\Gamma\vdash A\Rightarrow B:*^c\) | \(\Gamma\vdash A:*^c\)<br>\(\Gamma\vdash B:*^c\) |
| run step form | \(\Gamma\vdash\operatorname{RunStep}(A,B):*^c\) | \(\Gamma\vdash A:*^c\)<br>\(\Gamma\vdash B:*^c\) |

#### Value typing

| category | conclusion | premises |
| --- | --- | --- |
| value variable | \(\Gamma,x:A:*^c\vdash_v x^{*^c}:A\) | \(\operatorname{WF}(\Gamma,x:A:*^c)\) |
| value lambda | \(\Gamma\vdash_v\lambda^v x:A.M:A\Rightarrow B\) | \(\Gamma,x:A:*^c\vdash_c M:B\) |
| continue | \(\Gamma\vdash_v\operatorname{continue}_{A,B}(a):\operatorname{RunStep}(A,B)\) | \(\Gamma\vdash_v a:A\)<br>\(\Gamma\vdash B:*^c\) |
| finish | \(\Gamma\vdash_v\operatorname{finish}_{A,B}(b):\operatorname{RunStep}(A,B)\) | \(\Gamma\vdash A:*^c\)<br>\(\Gamma\vdash_v b:B\) |
| value conversion | \(\Gamma\vdash_v V:B\) | \(\Gamma\vdash_v V:A\)<br>\(\Gamma\vdash B:*^c\)<br>\(A\equiv_{\mathrm{ty}} B\) |

datatype constructor は全 argument が value のときに value を作る。Eliminator は branch
の評価を開始するので computation とする。

#### Computation typing

| category | conclusion | premises |
| --- | --- | --- |
| return | \(\Gamma\vdash_c\operatorname{return}(V):A\) | \(\Gamma\vdash_v V:A\) |
| application | \(\Gamma\vdash_c f\mathbin{@^c}a:B\) | \(\Gamma\vdash_v f:A\Rightarrow B\)<br>\(\Gamma\vdash_v a:A\) |
| bind | \(\Gamma\vdash_c\operatorname{bind}(M,x.N):B\) | \(\Gamma\vdash_c M:A\)<br>\(\Gamma,x:A:*^c\vdash_c N:B\) |
| case | \(\Gamma\vdash_c\operatorname{case}(V;\overline{c_i(\bar x_i)\mapsto M_i}):B\) | \(\Gamma\vdash_v V:D\)<br>各 branch が constructor field を value variable として bind し、\(B\) を返す |
| computation conversion | \(\Gamma\vdash_c M:B\) | \(\Gamma\vdash_c M:A\)<br>\(\Gamma\vdash B:*^c\)<br>\(A\equiv_{\mathrm{ty}} B\) |

これらの規則で computation を value とみなす coercion は与えない。逆方向は
\(\operatorname{return}\) を明示した場合にだけ使える。

#### Reflection typing

| category | conclusion | premises |
| --- | --- | --- |
| reflection type | \(\Gamma\vdash_D\operatorname{RfType}(A):*^s_0\) | \(\Gamma\vdash A:*^c\) |
| reflection value | \(\Gamma\vdash_D\operatorname{RfVal}_A(V):\operatorname{RfType}(A):*^s_0\) | \(\Gamma\vdash_v V:A\) |

例えば \(\Gamma\vdash_c M:A\) だけから
\(\Gamma\vdash_D\operatorname{RfVal}_A(M):\operatorname{RfType}(A):*^s_0\) は導出できない。特に
\(\operatorname{RfVal}_B(\operatorname{run}_{A,B}(f,a))\) は ill-formed である。

#### Application graph typing

| category | conclusion | premises |
| --- | --- | --- |
| app eval form | \(\Gamma\vdash_D\operatorname{AppEval}_{A,B}(g,a,b):*^p\) | \(\Gamma\vdash A:*^c\)<br>\(\Gamma\vdash B:*^c\)<br>\(\Gamma\vdash_D g:\operatorname{RfType}(A\Rightarrow B):*^s_0\)<br>\(\Gamma\vdash_D a:\operatorname{RfType}(A):*^s_0\)<br>\(\Gamma\vdash_D b:\operatorname{RfType}(B):*^s_0\) |
| app eval intro | \(\Gamma\vDash\operatorname{AppEval}_{A,B}(\operatorname{RfVal}(f),\operatorname{RfVal}(a),\operatorname{RfVal}(b))\) | \(\Gamma\vdash_v f:A\Rightarrow B\)<br>\(\Gamma\vdash_v a:A\)<br>\(\Gamma\vdash_v b:B\)<br>\(f\mathbin{@^c}a\Rightarrow_c^*\operatorname{return}(b)\) |

`app eval intro` の最後の premise は object-level の等式ではなく、compute abstract machine
の有限な評価履歴である。Kernel は履歴全体を proof term として保持せず、検査可能な
graph derivation または履歴の圧縮表現を保持できる。

この intro rule だけでは、任意の reflected state を仮定した accessibility 証明で
step function の branch を inversion できない。実際の体系では、\(\operatorname{AppEval}\) を
small-step 評価の帰納的 graph として定義し、return/application/bind/case/run ごとの
constructor と Prop 内への eliminator を与える必要がある。`app eval intro` はその帰納的
graph から導く admissible rule とする。

一般の effect を追加しない現在の compute calculus では、次の determinacy を目標とする。

\[
\operatorname{AppEval}_{A,B}(g,a,b_1)
\land
\operatorname{AppEval}_{A,B}(g,a,b_2)
\Longrightarrow
b_1=b_2.
\]

#### Accessibility

| category | conclusion | premises |
| --- | --- | --- |
| acc form | \(\Gamma\vdash_D\operatorname{Acc}_{A,B}(g,a):*^p\) | \(\Gamma\vdash_D g:\operatorname{RfType}(A\Rightarrow\operatorname{RunStep}(A,B)):*^s_0\)<br>\(\Gamma\vdash_D a:\operatorname{RfType}(A):*^s_0\) |
| acc intro | \(\Gamma\vDash\operatorname{Acc}_{A,B}(g,a)\) | \(\Gamma\vDash(b:\operatorname{RfType}(A))\to\operatorname{Next}_{A,B}(g,a,b)\to\operatorname{Acc}_{A,B}(g,b)\) |
| acc descent | \(\Gamma\vDash\operatorname{Acc}_{A,B}(g,b)\) | \(\Gamma\vDash\operatorname{Acc}_{A,B}(g,a)\)<br>\(\Gamma\vDash\operatorname{Next}_{A,B}(g,a,b)\) |

`acc intro` は後続状態がない場合も含む。Step function が `finish` を返す状態では
\(\operatorname{Next}(g,a,b)\) を満たす \(b\) がないため、premise は空虚に満たされる。

#### Run typing

| category | conclusion | premises |
| --- | --- | --- |
| run | \(\Gamma\vdash_c\operatorname{run}_{A,B}(f,a):B\) | \(\Gamma\vdash A:*^c\)<br>\(\Gamma\vdash B:*^c\)<br>\(\Gamma\vdash_v f:A\Rightarrow\operatorname{RunStep}(A,B)\)<br>\(\Gamma\vdash_v a:A\)<br>\(\Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)\) |
| run step | \(\Gamma\vdash_c\operatorname{runStep}_{A,B}(f,a,M):B\) | run の同じ signature<br>\(\Gamma\vdash_c M:\operatorname{RunStep}(A,B)\)<br>\(f\mathbin{@^c}a\Rightarrow_c^*M\)<br>\(\Gamma\vDash\operatorname{Terminates}_{A,B}(f,a)\) |

`run step` の評価履歴 premise は administrative term の invariant である。これにより、
第三 argument が \(\operatorname{return}(\operatorname{continue}(a'))\) に到達したとき、
`app eval intro` から \(\operatorname{Next}(\operatorname{RfVal}(f),\operatorname{RfVal}(a),
\operatorname{RfVal}(a'))\) を得られる。

## 設計の読み方

この体系は value type と computation type を別 sort にする完全な CBPV 構文ではない。
\(*^c\) を一つだけ保つため、次の二つを構文と judgement に吸収した
fine-grain call-by-value 形式の CBPV fragment である。

| full CBPV | この体系 |
| --- | --- |
| computation type \(F A\) | computation judgement \(\Gamma\vdash_c M:A\) |
| thunked function value \(U(A\to F B)\) | value arrow \(A\Rightarrow B\) |
| `thunk`/`force` | value lambda/application に暗黙化 |
| `return` | \(\operatorname{return}(V)\) |
| sequencing | \(\operatorname{bind}(M,x.N)\) |

この形でも、次の本質的な phase distinction は構文上保たれる。

- function と constructor は value である。
- application、elimination、general recursion は computation である。
- computation の結果は bind を通してだけ value variable になる。
- evaluation order は evaluation context が決める。
- reflection は value judgement を持つ項にだけ適用できる。

## `system.md` の Compute 側からの変更点

| 現在の形 | CBPV 化後 |
| --- | --- |
| \((*^c,*^c,*^c)\in\mathcal R\) | 一般 PTS product から外し、\(A\Rightarrow B\) を専用形成する |
| \(\Gamma\vdash m:A:*^c\) 一種類 | \(\Gamma\vdash_v V:A\) と \(\Gamma\vdash_c M:A\) |
| lambda body も通常項 | lambda は value、body は computation |
| application の結果は通常項 | application は computation |
| value をそのまま計算結果に使う | \(\operatorname{return}\) を明示する |
| 通常の compatible closure | evaluation context による弱 CBV reduction |
| \(\operatorname{run}(f,a):B:*^c\) | \(\operatorname{run}(f,a)\) は \(B\) を返す computation |
| \(\operatorname{RfTerm}_A(m)\) | value-only の \(\operatorname{RfVal}_A(V)\) |
| reflected function を Set function として適用 | closure は不透明に reflect し、振る舞いは \(\operatorname{AppEval}\) で記述 |
| `RunInv` は reflected application の等式 | `runStep` の評価履歴と \(\operatorname{AppEval}\) |

### 以前の一般再帰案で問題になった点

`run` の reduction は「一段計算が constructor まで到達する」という
\(\Rightarrow_c^*\) を root rule の side condition にしない。`runStep` へ入る無条件の
root rule と、第三 argument の小ステップ評価で進める。これにより、reduction
の定義が自分自身の推移閉包の confluence を先に要求する循環を避ける。

\(\Rightarrow_c^*\) が現れるのは `AppEval` の proof introduction と `runStep` の typing
invariant だけである。これらは次に実行する redex を選ぶ条件ではない。
履歴は実行と同時に一ステップずつ伸長し、kernel は与えられた有限 derivation の
各ステップを検査する。

また、step function の body を pure fragment に制限しない。すでに停止性が証明された
一般再帰関数 \(g:X\Rightarrow Y\) を別の step function から使うときは、

\[
\operatorname{let}\ y\leftarrow g\mathbin{@^c}x;M
\]

と書く。内側の `run` が結果を返すまで \(M\) は進まない。

Set 側の `Take` が Compute 側の `run` の状態に入る経路もない。`run` の状態は
value judgement を要求し、`Take` は Compute value typing を持たない。

## Reflection と計算結果

value-only reflection を厳密に守ると、次のような項は作れない。

\[
\operatorname{RfVal}_B
\left(\operatorname{run}_{A,B}(f,a)\right).
\]

一方、計算結果についての命題は graph で記述できる。`run` 全体の graph を
次の帰納的関係として定義する。

\[
\operatorname{RunEval}_{A,B}(g,a,b):*^p.
\]

\[
\frac{
\operatorname{AppEval}
\left(g,a,\widehat{\operatorname{finish}}(b)\right)
}{
\operatorname{RunEval}(g,a,b)
}
\qquad
\frac{
\operatorname{AppEval}
\left(g,a,\widehat{\operatorname{continue}}(a')\right)
\qquad
\operatorname{RunEval}(g,a',b)
}{
\operatorname{RunEval}(g,a,b)
}.
\]

これにより、「`run` の実行結果を Set 値として取り出す」のではなく、
「reflected input/output の間に実行 graph が成り立つ」という Prop を証明する。
`AppEval` の determinacy があれば、`RunEval` の結果の一意性も示せる。

\(\operatorname{Acc}(g,a)\) から、すべての入力で step graph が `continue` または
`finish` のどちらかに到達することを使えば、次を示すのが目標になる。

\[
\operatorname{Acc}_{A,B}(g,a)
\Longrightarrow
\exists b:\operatorname{RfType}(B).
\operatorname{RunEval}_{A,B}(g,a,b).
\]

## 例

#### Identity

\[
\begin{aligned}
\operatorname{id}
&:=\lambda^v x:A.\operatorname{return}(x),\\
\Gamma&\vdash_v\operatorname{id}:A\Rightarrow A,\\
\operatorname{id}\mathbin{@^c}V
&\Rightarrow_c\operatorname{return}(V).
\end{aligned}
\]

\(\operatorname{id}\) は value なので reflect できるが、その適用は computation なので
reflect できない。適用結果は次の graph で記述する。

\[
\operatorname{AppEval}_{A,A}
\left(
\operatorname{RfVal}(\operatorname{id}),
\operatorname{RfVal}(V),
\operatorname{RfVal}(V)
\right).
\]

#### Sequencing

\(f:A\Rightarrow B\), \(g:B\Rightarrow C\), \(a:A\) のとき、呼び出し順序は次のように
明示する。

\[
\operatorname{let}\ b\leftarrow f\mathbin{@^c}a;
g\mathbin{@^c}b.
\]

\(f\mathbin{@^c}a\) が \(\operatorname{return}(b)\) に到達するまで \(g\) は評価されない。

#### General recursion step

\[
f
:=
\lambda^v x:A.
\operatorname{return}
\left(
\operatorname{continue}_{A,B}(V_x)
\right)
:
A\Rightarrow\operatorname{RunStep}(A,B).
\]

\(V_x\) は \(x\) を free variable に持つ value とする。次状態を関数
\(h:A\Rightarrow A\) で計算するなら、
次のように bind する。

\[
f
:=
\lambda^v x:A.
\operatorname{let}\ x'\leftarrow h\mathbin{@^c}x;
\operatorname{return}
\left(
\operatorname{continue}_{A,B}(x')
\right).
\]

この形では、\(h\mathbin{@^c}x\) が返る前に `continue` を構築できない。

## Subject reduction で必要な事実

\(\operatorname{runStep}\) の `continue` rule が subject reduction を保つためには、次の
bridge lemma が必要である。

\[
\begin{aligned}
&\Gamma\vdash_v f:A\Rightarrow\operatorname{RunStep}(A,B),\\
&\Gamma\vdash_v a:A,\\
&\Gamma\vdash_v a':A,\\
&f\mathbin{@^c}a
\Rightarrow_c^*
\operatorname{return}(\operatorname{continue}_{A,B}(a'))
\end{aligned}
\]

から、

\[
\Gamma\vDash
\operatorname{Next}_{A,B}
\left(
\operatorname{RfVal}(f),
\operatorname{RfVal}(a),
\operatorname{RfVal}(a')
\right)
\]

が得られる。そして、

\[
\operatorname{Acc}(g,\operatorname{RfVal}(a))
\land
\operatorname{Next}(g,\operatorname{RfVal}(a),\operatorname{RfVal}(a'))
\]

に `acc descent` を適用して、次の \(\operatorname{run}(f,a')\) が要求する停止証明を
得る。

## メタ理論の課題

最低限、次を示す必要がある。

1. **Value substitution**
   \(\Gamma,x:A\vdash_c M:B\) と \(\Gamma\vdash_v V:A\) から
   \(\Gamma\vdash_c M[x:=V]:B\) が得られる。
2. **Compute preservation**
   \(\Gamma\vdash_c M:A\) と \(M\Rightarrow_c M'\) から
   \(\Gamma\vdash_c M':A\) が得られる。
3. **Determinism**
   \(M\Rightarrow_c M_1\) と \(M\Rightarrow_c M_2\) から \(M_1=M_2\) が得られる。
4. **Graph soundness**
   \(\operatorname{AppEval}(\operatorname{RfVal}(f),\operatorname{RfVal}(a),b)\) が provable なら、
   \(f\mathbin{@^c}a\) は \(b\) に対応する value を返す。
5. **Graph completeness on reflected values**
   \(f\mathbin{@^c}a\Rightarrow_c^*\operatorname{return}(b)\) なら、対応する
   \(\operatorname{AppEval}\) が provable である。
6. **Run preservation**
   `AppEval` と `Acc` の bridge lemma を使って、`runStep-continue` が型と停止証明を
   保存する。
7. **Conservativity of the description layer**
   Compute value と graph の追加によって、新しい閉じた Set/Prop の定理が根拠なく
   生じない。
8. **Graph induction and inversion**
   `AppEval` を return/application/bind/case/run の小ステップに沿う帰納的 graph として
   内部化し、reflected state 上の accessibility 証明で step function の branch を
   inversion できるようにする。
9. **Adequacy of reflected value types**
   状態に使う datatype について、\(\operatorname{RfType}(A)\) の各要素が Compute value
   の reflection に対応すること、または graph rule が reflection の image 外でも
   全域に定義されることを示す。

## この案で得られること

- Compute 側に追加する proper sort は \(*^c\) 一つのままである。
- value/computation の区別は raw syntax と typing judgement の両方で検査できる。
- application と bind により、nested computation の評価順序が明示的になる。
- `run` は value を作る constructor ではなく、value を返す computation になる。
- reflection は value-only であり、計算を Set 側の definitional equality に混入させない。
- 計算の振る舞いは extensional function reflection ではなく、Prop 側の evaluation graph
  と accessibility で検証できる。

一方で、`AppEval` をどの程度 primitive にするか、その derivation を kernel がどの形で
検査するかは未確定である。次に固めるべき点は、`AppEval` を evaluation trace の
帰納的 graph として内部化したときの、intro/elim rule と証明消去である。
