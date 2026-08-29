## 体系定義

ここでは、現行体系の compute sort \(*^c\) だけを CBPV 風に分解する。
Set と Prop の PTS 部分は変更しない。特に、この分解を Set 側へ持ち込まず、
reflection を通過した後は value と computation を同じ Set 項として扱う。

目標は次の三点である。

- compute 内では、値を作る構文と計算を進める構文を区別する。
- \(\operatorname{run}\)、\(\operatorname{runCase}\)、
  \(\operatorname{continue}\)、\(\operatorname{finish}\) は compute にだけ置く。
- Set 側では \(\operatorname{RfTerm}\) が両 phase を同じ型へ埋め込み、
  計算用の構文を Set の constructor として複製しない。

以下で提案するのは、effect のない決定的な一般再帰を対象とする最小の CBPV 化である。

### sort

sort の集合と axiom は現行体系と同じく、

\[
\begin{aligned}
\mathcal S
&=
\{*^s_i,\sq^s_i\mid i\in\mathbb N\}
\cup\{*^p,\sq^p\}
\cup\{*^c,\sq^c\},\\
\mathcal A
&=
\{(*^s_i,\sq^s_i)\}
\cup\{(*^p,\sq^p)\}
\cup\{(*^c,\sq^c)\}
\end{aligned}
\]

とする。ただし、compute の関数を普通の PTS の積で作らない。
すなわち、積の relation から

\[
(*^c,*^c,*^c)
\]

を外し、代わりに compute 専用の非依存関数型

\[
A\Rightarrow B:*^c
\]

を導入する。\(\sq^c\) は kind であり、項を分類する proper sort は
\(*^c\) 一つだけである。

この \(A\Rightarrow B\) は、通常の CBPV の記法では概ね
\(U(A\to F B)\) に相当する。ただし本稿では \(F\) と \(U\) を
構文として露出させず、typing judgement によって phase を区別する。

### context と judgement

compute の context に入る項変数は value 変数だけとする。

\[
\Delta::=\varnothing\mid\Delta,x:A
\]

compute 部分では、次の judgement を用いる。

\[
\begin{array}{ll}
\Gamma;\Delta\vdash A:*^c
& \text{\(A\) は compute type},\\
\Gamma;\Delta\vdash_v V:A
& \text{\(V\) は \(A\) の value},\\
\Gamma;\Delta\vdash_c M:A
& \text{\(M\) は \(A\) を返す computation},\\
\Gamma;\Delta\vdash_s T:*^s_i
& \text{\(T\) は Set type},\\
\Gamma;\Delta\vdash_s t:T:*^s_i
& \text{\(t\) は \(T\) の Set 項},\\
\Gamma;\Delta\vdash_p P
& \text{\(P\) は proposition},\\
\Gamma;\Delta\vDash P
& \text{\(P\) は証明可能}.
\end{array}
\]

\(\Gamma\) は従来どおり Set と Prop に関する外側の context を表す。
mixed context \(\Gamma;\Delta\) を使うのは、例えば compute value 変数
\(x:A\) を payload に持つ
\(\operatorname{RfTerm}_A(x)\) について Set の命題を書くためである。
Set の裸の項から \(x\) を直接参照することはできず、compute 変数は
\(\operatorname{RfTerm}\) の payload 内だけに出現できる。

値変数だけを \(\Delta\) に置くため、computation を substitution
できる位置は \(\operatorname{bind}\) によって明示される。

### compute type と構文

compute type は、少なくとも次の形を持つ。

\[
A,B::=I^c(\vec A)\mid A\Rightarrow B\mid
\operatorname{RunStep}(A,B).
\]

\(I^c\) は compute 側の通常の datatype を表す。

value と computation の構文を分ける。

\[
\begin{aligned}
V,W
::={}&x
\mid\lambda^v x:A.M
\mid C(\vec V)\\
&\mid\operatorname{continue}_{A,B}(V)
\mid\operatorname{finish}_{A,B}(V),\\[2mm]
M,N
::={}&\operatorname{return}(V)
\mid V@^cW
\mid\operatorname{bind}(M,x.N)\\
&\mid\operatorname{case}(V;\overline{C(\vec x)\mapsto M_C})\\
&\mid\operatorname{run}_{A,B}(V,W)
\mid\operatorname{runCase}_{A,B}(V,W,M).
\end{aligned}
\]

\(\lambda^v\) 自身は value だが、その本体は computation である。
\(\operatorname{continue}\) と \(\operatorname{finish}\) も
\(\operatorname{RunStep}(A,B)\) の value constructor である。
一方、関数適用、case、run は computation である。

### compute typing

主要な規則は次のとおりである。

\[
\frac{
 \Gamma;\Delta,x:A\vdash_c M:B
}{
 \Gamma;\Delta\vdash_v\lambda^v x:A.M:A\Rightarrow B
}
\tag{Fun-I}
\]

\[
\frac{
 \Gamma;\Delta\vdash_v f:A\Rightarrow B
 \qquad
 \Gamma;\Delta\vdash_v a:A
}{
 \Gamma;\Delta\vdash_c f@^c a:B
}
\tag{Fun-E}
\]

\[
\frac{\Gamma;\Delta\vdash_v V:A}
     {\Gamma;\Delta\vdash_c\operatorname{return}(V):A}
\tag{Return}
\]

\[
\frac{
 \Gamma;\Delta\vdash_c M:A
 \qquad
 \Gamma;\Delta,x:A\vdash_c N:B
}{
 \Gamma;\Delta\vdash_c\operatorname{bind}(M,x.N):B
}
\tag{Bind}
\]

\[
\frac{\Gamma;\Delta\vdash_v a:A}
     {\Gamma;\Delta\vdash_v
       \operatorname{continue}_{A,B}(a):
       \operatorname{RunStep}(A,B)}
\tag{Continue}
\]

\[
\frac{\Gamma;\Delta\vdash_v b:B}
     {\Gamma;\Delta\vdash_v
       \operatorname{finish}_{A,B}(b):
       \operatorname{RunStep}(A,B)}
\tag{Finish}
\]

case の各 branch は同じ型の computation とする。特に、
constructor の引数は value 変数として branch の context に入る。

### compute reduction

評価 context は

\[
E::=[\,]
\mid\operatorname{bind}(E,x.M)
\mid\operatorname{runCase}_{A,B}(f,a,E)
\]

とする。root reduction は次である。

\[
(\lambda^v x:A.M)@^cV
\longrightarrow_c
M[x:=V]
\tag{Beta-v}
\]

\[
\operatorname{bind}(\operatorname{return}(V),x.M)
\longrightarrow_c
M[x:=V]
\tag{Bind-return}
\]

\[
\operatorname{case}
\left(
 C_i(\vec V);
 \overline{C_j(\vec x_j)\mapsto M_j}
\right)
\longrightarrow_c
M_i[\vec x_i:=\vec V]
\tag{Case}
\]

そして \(M\longrightarrow_c M'\) なら
\(E[M]\longrightarrow_c E[M']\) とする。

これは weak call-by-value である。value、\(\lambda^v\) の本体、
\(\operatorname{return}\) の中、選択されていない branch の中では
reduction しない。

### 一般再帰

\(\operatorname{run}\) の制御も compute reduction だけで行う。

\[
\operatorname{run}_{A,B}(f,a)
\longrightarrow_c
\operatorname{runCase}_{A,B}(f,a,f@^ca)
\tag{Run-enter}
\]

\[
\operatorname{runCase}_{A,B}
\left(
 f,a,\operatorname{return}
   (\operatorname{continue}_{A,B}(a'))
\right)
\longrightarrow_c
\operatorname{run}_{A,B}(f,a')
\tag{Run-continue}
\]

\[
\operatorname{runCase}_{A,B}
\left(
 f,a,\operatorname{return}
   (\operatorname{finish}_{A,B}(b))
\right)
\longrightarrow_c
\operatorname{return}(b).
\tag{Run-finish}
\]

第三引数が computation になった点が現行体系との構文上の差である。
したがって、step 関数が返した computation は
\(\operatorname{runCase}\) の内側で先に評価され、その結果が
\(\operatorname{return}(\operatorname{continue}(a'))\) または
\(\operatorname{return}(\operatorname{finish}(b))\) になってから分岐する。

### phase を消去する reflection

Set 側へ公開する構文は

\[
\operatorname{RfType}(A)
\qquad
\operatorname{RfTerm}_A(e)
\]

だけとする。payload \(e\) は value \(V\) でも computation \(M\) でもよい。
ただし両者の Set 側の型は同じである。

\[
\frac{\Gamma;\Delta\vdash A:*^c}
     {\Gamma;\Delta\vdash_s\operatorname{RfType}(A):*^s_0}
\tag{Rf-Type}
\]

\[
\frac{\Gamma;\Delta\vdash_v V:A}
     {\Gamma;\Delta\vdash_s
       \operatorname{RfTerm}_A(V):
       \operatorname{RfType}(A):*^s_0}
\tag{Rf-Value}
\]

\[
\frac{\Gamma;\Delta\vdash_c M:A}
     {\Gamma;\Delta\vdash_s
       \operatorname{RfTerm}_A(M):
       \operatorname{RfType}(A):*^s_0}
\tag{Rf-Compute}
\]

ここで \(\operatorname{RfTerm}_A(M)\) は computation constructor の
structural reflection ではない。compute の項を opaque な payload として
Set 項に glue する境界である。したがって Set の term grammar には、
\(\operatorname{run}^s\)、\(\operatorname{runCase}^s\)、
\(\operatorname{continue}^s\)、\(\operatorname{finish}^s\) のような項を
追加しない。

この意味で、reflection の source を value だけに制限するのではなく、
reflection の結果を一種類に制限する。literal に
\(\operatorname{RfTerm}\) の source まで value だけにすると、
\(\operatorname{run}(f,a)\) 自体を Set の結果として取り出せない。
一方、この規則なら Set 側に computation phase を新設する必要はない。

reflection に関する reduction は次である。

\[
\operatorname{RfType}(A\Rightarrow B)
\longrightarrow
\operatorname{RfType}(A)\to\operatorname{RfType}(B).
\tag{Rf-Arrow}
\]

\[
\operatorname{RfTerm}_{A\Rightarrow B}(f)
@
\operatorname{RfTerm}_{A}(a)
\longrightarrow
\operatorname{RfTerm}_{B}(f@^ca).
\tag{Rf-App}
\]

ここで \(f\) と \(a\) はそれぞれ compute function value と compute value
である。したがって右辺の payload は well-typed な computation になる。

\[
\operatorname{RfTerm}_{A}(\operatorname{return}(V))
\longrightarrow
\operatorname{RfTerm}_{A}(V).
\tag{Rf-Return}
\]

\[
\frac{M\longrightarrow_cM'}
     {\operatorname{RfTerm}_{A}(M)
      \longrightarrow
      \operatorname{RfTerm}_{A}(M')}.
\tag{Rf-Cong}
\]

\(\operatorname{RfTerm}\) の外側は始めから Set 項であり、
内側だけが compute reduction を進める。例えば

\[
\begin{aligned}
\operatorname{RfTerm}_{B}(\operatorname{run}(f,a))
&\longrightarrow^*
\operatorname{RfTerm}_{B}(\operatorname{return}(b))\\
&\longrightarrow
\operatorname{RfTerm}_{B}(b).
\end{aligned}
\]

ここには Set 側の run 規則も、Set 側の continue/finish も現れない。

### datatype の reflection

通常の compute datatype \(I^c\) には、現行体系と同様に structural な
reflection 規則を生成してよい。

\[
\operatorname{RfType}(I^c(\vec A))
\longrightarrow
I^s(\operatorname{RfType}(\vec A))
\]

\[
\operatorname{RfTerm}_{I^c}
\left(C^c(\vec V)\right)
\longrightarrow
C^s\left(\operatorname{RfTerm}(\vec V)\right).
\]

これにより、run の最終結果が通常の datatype の value なら、
Set 側の constructor まで計算できる。

ただし \(\operatorname{RunStep}(A,B)\) は実行制御のための内部型であり、
この structural reflection の対象から外す。
\(\operatorname{RfType}(\operatorname{RunStep}(A,B))\) と
\(\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}(e)\) は
glued carrier としてだけ使う。したがって
\(\operatorname{continue}\) や \(\operatorname{finish}\) が
Set constructor として露出することはない。

### accessibility

step 関数は

\[
f:A\Rightarrow\operatorname{RunStep}(A,B)
\]

という value である。補助関数を

\[
\operatorname{continueFun}_{A,B}
:=
\lambda^v z:A.
\operatorname{return}
\left(\operatorname{continue}_{A,B}(z)\right)
\]

とする。

Set 上の一ステップ関係を

\[
\begin{aligned}
\operatorname{Next}_{A,B}(f,b,a)
:={}&
\operatorname{RfTerm}_{A\Rightarrow\operatorname{RunStep}(A,B)}(f)
@a\\
&=
\operatorname{RfTerm}_{A\Rightarrow\operatorname{RunStep}(A,B)}
(\operatorname{continueFun}_{A,B})
@b
\end{aligned}
\]

で定義する。ここで \(a,b:\operatorname{RfType}(A)\) は Set 項である。
\(\operatorname{Acc}_{A,B}(f,a)\) は、この関係に関する accessibility
とする。

\[
\frac{
 \Gamma;\Delta\vdash_v
 f:A\Rightarrow\operatorname{RunStep}(A,B)
 \qquad
 \Gamma;\Delta\vdash_s
 a:\operatorname{RfType}(A):*^s_0
}{
 \Gamma;\Delta\vdash_p\operatorname{Acc}_{A,B}(f,a)
}
\tag{Acc-Form}
\]

\[
\frac{
 \Gamma,x:\operatorname{RfType}(A);\Delta
 \vDash
 \operatorname{Next}_{A,B}(f,x,a)
 \to
 \operatorname{Acc}_{A,B}(f,x)
}{
 \Gamma;\Delta\vDash\operatorname{Acc}_{A,B}(f,a)
}
\tag{Acc-Intro}
\]

この規則では \(x\) を conclusion の context に現れない fresh な Set 変数
とする。これは、すべての predecessor が accessible なら \(a\) も
accessible であるという通常の Acc introduction である。

\[
\frac{
 \Gamma;\Delta\vDash\operatorname{Acc}_{A,B}(f,a)
 \qquad
 \Gamma;\Delta\vDash\operatorname{Next}_{A,B}(f,b,a)
}{
 \Gamma;\Delta\vDash\operatorname{Acc}_{A,B}(f,b)
}
\tag{Acc-Descent}
\]

\[
\operatorname{Terminates}_{A,B}(f,a)
:=
\operatorname{Acc}_{A,B}
\left(f,\operatorname{RfTerm}_A(a)\right).
\]

\(\operatorname{Next}\) の右辺は

\[
\begin{aligned}
&
\operatorname{RfTerm}_{A\Rightarrow\operatorname{RunStep}(A,B)}
(\operatorname{continueFun}_{A,B})
@
\operatorname{RfTerm}_{A}(a')\\
&\longrightarrow
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
\left(\operatorname{continueFun}_{A,B}@^ca'\right)\\
&\longrightarrow
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
\left(
 \operatorname{return}(\operatorname{continue}_{A,B}(a'))
\right)\\
&\longrightarrow
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
\left(\operatorname{continue}_{A,B}(a')\right)
\end{aligned}
\]

と計算する。最後の項も glued reflection であって、
Set 側に continue constructor を導入したものではない。

### run の typing と invariant

run の規則を

\[
\frac{
 \begin{array}{c}
 \Gamma;\Delta\vdash_v f:
 A\Rightarrow\operatorname{RunStep}(A,B)
 \qquad
 \Gamma;\Delta\vdash_v a:A\\
 \Gamma;\Delta\vDash\operatorname{Terminates}_{A,B}(f,a)
 \end{array}
}{
 \Gamma;\Delta\vdash_c
 \operatorname{run}_{A,B}(f,a):B
}
\tag{Run}
\]

とする。

\(\operatorname{runCase}\) が保持する invariant は

\[
\begin{aligned}
\operatorname{RunInv}_{A,B}(f,a,M)
:={}&
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}
(f@^ca)\\
&=
\operatorname{RfTerm}_{\operatorname{RunStep}(A,B)}(M)
\end{aligned}
\]

である。両辺は同じ Set 型を持つので、ここでも Set 側に
computation 用の equality や evaluation relation は要らない。

\[
\frac{
 \begin{array}{c}
 \Gamma;\Delta\vdash_v f:
 A\Rightarrow\operatorname{RunStep}(A,B)
 \qquad
 \Gamma;\Delta\vdash_v a:A\\
 \Gamma;\Delta\vdash_c M:\operatorname{RunStep}(A,B)\\
 \Gamma;\Delta\vDash\operatorname{Terminates}_{A,B}(f,a)
 \qquad
 \Gamma;\Delta\vDash\operatorname{RunInv}_{A,B}(f,a,M)
 \end{array}
}{
 \Gamma;\Delta\vdash_c
 \operatorname{runCase}_{A,B}(f,a,M):B
}
\tag{RunCase}
\]

\(\operatorname{Run-enter}\) の直後は第三引数が \(f@^ca\) なので、
\(\operatorname{RunInv}\) は reflexivity から得られる。

\(\operatorname{Run-continue}\) の source では invariant と
\(\operatorname{Rf-Return}\) から

\[
\operatorname{RfTerm}(f@^ca)
=
\operatorname{RfTerm}(\operatorname{continue}(a'))
\]

を得る。一方、
\(\operatorname{Next}(f,\operatorname{RfTerm}(a'),
\operatorname{RfTerm}(a))\) の右辺も、先ほどの reflection reduction
によって同じ
\(\operatorname{RfTerm}(\operatorname{continue}(a'))\) へ簡約する。
よって equality の conversion と Acc descent から

\[
\operatorname{Terminates}_{A,B}(f,a')
\]

が得られ、reduct の
\(\operatorname{run}_{A,B}(f,a')\) を型付けできる。

\(\operatorname{Run-finish}\) では reduct が
\(\operatorname{return}(b):B\) なので、そのまま preservation が従う。

step 関数の本体を run-free な fragment に制限する必要はない。
すでに termination を証明した別の run を
\(\operatorname{bind}\) で実行し、その value を使って
\(\operatorname{continue}\) または \(\operatorname{finish}\) を返せる。
この再利用を保つため、pure という構文的 side condition は導入しない。

### Set から見える結果

\(\Gamma;\varnothing\vdash_c\operatorname{run}(f,a):B\) なら、

\[
\Gamma;\varnothing\vdash_s
\operatorname{RfTerm}_B(\operatorname{run}(f,a)):
\operatorname{RfType}(B):*^s_0
\]

である。この一項だけが Set 側の観測点になる。

compute 内では

\[
\text{value}\quad\neq\quad\text{computation}
\]

だが、reflection 後は

\[
\operatorname{RfTerm}_A(V),
\operatorname{RfTerm}_A(M)
:
\operatorname{RfType}(A)
\]

となり、Set の型には phase の違いが残らない。

\(\operatorname{RfType}(A\Rightarrow B)\) は Set の関数型へ簡約するので、
reflected function は Set 項として適用できる。ただし
\(\operatorname{Rf-App}\) が計算するのは引数が
\(\operatorname{RfTerm}_A(a)\) の形である場合だけである。
例えば \(\operatorname{Take}\) で作った任意の Set 項にも型としては適用
できるが、それを compute の value として逆向きに取り込んではならない。
この非対称性は現行体系と同じである。

したがって、\(\operatorname{Take}\)、\(\Power\)、\(\Proof\)、refinement
などの Set/Prop の項が run の状態や step 関数の引数へ混入することはない。
reflection は compute から Set への一方向の境界である。

## 必要な性質

この案を core calculus に採用するには、少なくとも次を示す必要がある。

1. value substitution:
   \(\Gamma;\Delta,x:A\vdash_\alpha e:T\) と
   \(\Gamma;\Delta\vdash_vV:A\) から
   \(\Gamma;\Delta\vdash_\alpha e[x:=V]:T\)。
2. compute preservation:
   \(\Gamma;\Delta\vdash_cM:A\) かつ
   \(M\longrightarrow_cM'\) なら
   \(\Gamma;\Delta\vdash_cM':A\)。
3. compute reduction の determinism。
4. \(\operatorname{Rf-App}\)、\(\operatorname{Rf-Return}\)、
   \(\operatorname{Rf-Cong}\) の Set 側での preservation。
5. compute reduction による \(\operatorname{RunInv}\) の保存。
6. \(\operatorname{RunCase}\) の三つの reduction に対する subject reduction。
7. reflection と Set reduction の critical pair を含む confluence。
8. 空 context、または termination assumption が意味論的に妥当な context
   における、reflected closed computation の normalization。
9. accessibility と glued reflection を解釈する model の soundness。

特に、根で使える conditional rule
\(f@^ca\longrightarrow_c^*\operatorname{return}(\operatorname{continue}(a'))\)
を run の前提に置かないことが重要である。その形では confluence の証明が
run 自身の多段簡約に依存しやすい。\(\operatorname{runCase}\) を
administrative term として残せば、通常の evaluation context と
局所的な root rule で制御できる。

また、偽の accessibility assumption を context に置けば、停止しない
run を型付けできる可能性は残る。したがって normalization の主張範囲は、
空 context または assumption の意味論的妥当性を要求する必要がある。
これは現行体系と同じ制約である。

## 現行体系との差

| 項目 | 現行体系 | この案 |
| --- | --- | --- |
| compute の項 | 一種類 | value と computation を区別 |
| compute 関数 | PTS の \(A\to B\) | 専用の \(A\Rightarrow B\) |
| 関数本体 | 通常項 | computation |
| step の返却 | \(\operatorname{RunStep}\) の項 | \(\operatorname{return}(\operatorname{RunStep}\text{ value})\) |
| runCase の第三引数 | 通常の compute 項 | computation |
| Set の reflection | 一つの \(\operatorname{RfTerm}\) | 同じく一つの \(\operatorname{RfTerm}\) |
| Set の value/computation | 区別なし | 区別なし |
| Set の run/continue/finish | なし | なし |

つまり変更は \(*^c\) の内部に閉じる。compute 側では CBPV の phase
distinction によって評価順序を明示し、Set 側では
\(\operatorname{RfTerm}\) がその distinction を消去する。
\(\operatorname{run}\) などを Set に reflection するのではなく、
それらを含む compute payload の簡約だけを Set 項の内側で許すのが、
現行体系の設計を保ったまま CBPV 化する方法である。
