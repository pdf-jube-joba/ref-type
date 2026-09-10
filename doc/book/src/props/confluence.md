# Core calculus の合流性

対象は [system.md](../system.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
ここで示すのは補助 reduction の合流性である。元の reduction の合流性や subject reduction は結論しない。
代入の合成則は[構文的補題](metatheory.md#substitution)を使う。
以下の本文は現行の Set/Prop の三構文に適用する。
式中で省略した \(\Pi,\lambda,@,\operatorname{prec}\) の rule label・sort 添字は固定し、
全 congruence rule はそれらを保持する。
beta の lambda と application は同じ \(r\) を持つ場合にだけ root とする。
Pred の reduct は \(p_i\)、prec の branch application は \(h_{i,\sigma}\)、
run の application は \(s^{i,i}\) を持つ。
補助規則で外すのは、下に明記する constructor の型引数の一致条件だけである。

<a id="auxiliary-reduction"></a>

## Box-free raw conversion の共通簡約先

\(\to_0\) を Box-free core の raw reduction とする。
`prec` と `runCase` の左辺では、同じ型添字が複数回現れる。
そのため、この規則をそのまま left-linear と呼ぶことはできない。

補助 reduction \(\rightsquigarrow\) を次のように定義する。
beta、Pred、run の規則は \(\to_0\) と同じとし、次の四規則では
内側と外側の型添字の一致を要求しない。

\[
\begin{aligned}
\operatorname{prec}_{\operatorname{RunStep}(A,B)}
(x^s.P,c,d,\operatorname{continue}_{C,D}(a))&\rightsquigarrow c@a,\\
\operatorname{prec}_{\operatorname{RunStep}(A,B)}
(x^s.P,c,d,\operatorname{finish}_{C,D}(b))&\rightsquigarrow d@b,\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{continue}_{C,D}(a'))
&\rightsquigarrow\operatorname{run}_{A,B}(f,a'),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{C,D}(b))
&\rightsquigarrow b.
\end{aligned}
\]

全 Set constructor で compatible closure を取る。
これは証明に使う補助関係であって、object calculus の conversion rule を変更しない。
定義から \(\to_0\ \subseteq\ \rightsquigarrow\) である。

### Parallel reduction

\(t\Rrightarrow u\) を次の規則で生成する。

1. sort と変数は自分自身へ写る。
2. 各 constructor について、全引数を並列に簡約する congruence rule を置く。
   束縛 body は同じ局所変数のもとで簡約する。
3. beta は
   \[
   (\lambda_r x:A.m)@_r a\Rrightarrow m'[x:=a']
   \quad(A\Rrightarrow A',\ m\Rrightarrow m',\ a\Rrightarrow a').
   \]
4. Pred には次の二規則を置く。
   \[
   \begin{aligned}
   \Pred(A,\{x:B\mid P\},a)&\Rrightarrow(\lambda x:B'.P')@a',\\
   \Pred(A,\{x:B\mid P\},a)&\Rrightarrow P'[x:=a'].
   \end{aligned}
   \]
   いずれも \(A\Rrightarrow A'\)、\(B\Rrightarrow B'\)、
   \(P\Rrightarrow P'\)、\(a\Rrightarrow a'\) を premise とする。
5. 残りの各 \(\rightsquigarrow\) root rule について、左辺の metavariable
   ごとに並列簡約を行い、右辺ではその簡約後の値を使う規則を置く。
   例として run では
   \[
   \operatorname{run}_{A,B}(f,a)\Rrightarrow
   \operatorname{runCase}_{A',B'}(f',a',f'@a').
   \]
   この一回の規則では、新しく作った \(f'@a'\) をさらに簡約しない。

構造帰納法により \(t\Rrightarrow t\)。また、

\[
\rightsquigarrow\ \subseteq\ \Rrightarrow\ \subseteq\ \rightsquigarrow^*.
\tag{parallel-sandwich}
\]

左の包含は、非選択引数を reflexive に並列簡約すればよい。
右の包含は並列導出の帰納法による。congruence の場合は各引数の有限列を
順に実行する。root の場合は各引数の有限列の後で root を実行する。
Pred の第二規則だけは最後に Pred root と beta の二段を実行する。

さらに、

\[
t\Rrightarrow t',\quad u\Rrightarrow u'
\quad\Longrightarrow\quad
t[x:=u]\Rrightarrow t'[x:=u'].
\tag{parallel-subst}
\]

**証明。** \(t\Rrightarrow t'\) の導出帰納法。
変数の場合は \(u\Rrightarrow u'\) または変数の reflexivity。
congruence では引数ごとの帰納法を使う。
beta と Pred の第二規則では、右辺の二つの代入を `subst-comp` で交換する。
残りの root では metavariable の置換と項の代入が構造的に可換である。
run が \(f,a\) を複製する場合も、同じ \(f',a'\) を両方に使えばよい。□

### Complete development

\(t^\star\) を構造再帰で定義する。root に一致するときは以下を優先する。

\[
\begin{aligned}
((\lambda_r x:A.m)@_r a)^\star&=m^\star[x:=a^\star],\\
\Pred(A,\{x:B\mid P\},a)^\star&=P^\star[x:=a^\star],\\
\operatorname{prec}_{\operatorname{RunStep}(A,B)}
(x^s.P,c,d,\operatorname{continue}_{C,D}(a))^\star&=c^\star @a^\star,\\
\operatorname{prec}_{\operatorname{RunStep}(A,B)}
(x^s.P,c,d,\operatorname{finish}_{C,D}(b))^\star&=d^\star @b^\star,\\
\operatorname{run}_{A,B}(f,a)^\star
&=\operatorname{runCase}_{A^\star,B^\star}
(f^\star,a^\star,f^\star @a^\star),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{continue}_{C,D}(a'))^\star
&=\operatorname{run}_{A^\star,B^\star}(f^\star,(a')^\star),\\
\operatorname{runCase}_{A,B}(f,a,\operatorname{finish}_{C,D}(b))^\star
&=b^\star.
\end{aligned}
\]

その他の形では constructor を保ち、引数に再帰的に作用させる。
右辺に新しく現れた redex の complete development は行わないので、
この定義は停止する構造再帰である。

**補題。** \(t\Rrightarrow u\) なら \(u\Rrightarrow t^\star\)。

**証明。** \(t\) の構造帰納法。
root に一致しない場合、並列導出は congruence なので各引数の帰納法を使う。
root に一致する場合は、導出が congruence か root かで分ける。

- congruence の場合、root を認識する lambda、subset、continue、finish の
  constructor はその congruence によって失われない。引数の帰納法を premise として
  並列 root を適用すれば \(t^\star\) を得る。
  ここで内外の型添字の一致を要求しないことが必要である。
  beta の二つの rule label は congruence で変化しないため、同じ root に一致し続ける。
- beta root の場合は `parallel-subst` を使う。
- Pred の第一 root の場合、得られた application に並列 beta を適用する。
  第二 root の場合は `parallel-subst` を使う。
- prec、run、runCase の root の場合は、右辺の各引数を帰納法で簡約する。
  run で複製された引数には同じ帰納法の結果を使う。
  右辺に作られた application や run には congruence を選べばよい。

これで全 constructor と全 root を尽くした。□

従って \(\Rrightarrow\) は diamond property を持つ。
有限列に関する二重帰納法、または diamond の有限格子を並べることにより
\(\Rrightarrow^*\) は confluent。
`parallel-sandwich` より \(\rightsquigarrow^*\) も confluent である。
任意の有限 zigzag の長さについて帰納法を行うと、

\[
t\equiv_0 u
\quad\Longrightarrow\quad
\exists w.\ t\rightsquigarrow^*w\ \land\ u\rightsquigarrow^*w.
\tag{aux-join}
\]

この結論は **補助関係での共通簡約先** であり、
\(\to_0\) 自体の合流性を証明した、と読み替えてはならない。
とくに、この段階では \(w\) の typing は保証されない。
後で[補助体系の SR](subject_reduction.md#typed-join)を用いると、
両端の typing から \(w\) と途中の項の \(\mathcal S_+\) における typing を得られる。

### Head discrimination と injectivity

sort、変数、Power、Ty、product、RunStep は、
\(\rightsquigarrow\) によって自分の外側の constructor を失わない。
従って `aux-join` から以下が従う。

- 異なる sort 定数は \(\equiv_0\) でない。
- 自由変数は sort、Ty、Power、product、RunStep と \(\equiv_0\) でない。
- Ty、Power、product、RunStep の異なる head 同士は \(\equiv_0\) でない。
- \(\Power A\equiv_0\Power B\) なら \(A,B\) は補助関係で共通簡約先を持つ。
- 二つの product が \(\equiv_0\) なら、rule label と binder の sort 注釈は一致し、
  alpha-renaming 後の domain 同士、body 同士はそれぞれ補助関係で共通簡約先を持つ。

最後の二項について、ここで得た引数の join を直ちに
\(A\equiv_0B\) 等へ戻すことはできない。
補助 step の original conversion への可換性は別途必要である。
この区別は subject reduction の証明における循環を避けるために重要である。

## 旧記法による検討メモ

以下は、RunStep などを含める前の規則・記法による合流性の検討メモである。
現行 core の定義・証明としては、上の節を参照する。

拡張した体系として、部分型・べき・述語・存在・take を入れてた。
これの confluence を示す。

Tait-Martin-Lof の parallel reduction と Takahashi の \(M^*\) を使えばできそう。
term はだいたい cong にやってるが、次のものだけ追加されている。
- \(\Pred (A, \{x: t \mid P \}) \rightarrow^\beta \lambda x:t. P\)

これに合わせて、 parallel reduction と \(M^*\) は次のものを入れておけばいい。
- \(\Pred (A, \{x: t \mid P\}) \Rightarrow \lambda x: t'. P'\) if \(t \Rightarrow t', P \Rightarrow P', A \Rightarrow A'\)
- \(\Pred (A, B) \Rightarrow \Pred(A', B')\) if \(A \Rightarrow A', B \Rightarrow B'\)
- \((\Pred (A, \{x: t \mid P\}))^* = \lambda x: t^*. P^*\) 

としておく。

\(\{A \mid P\}\) を使う場合は次のようにする。
- \(\Pred(A, \{B \mid P\}) \to_\beta P\)
- \(\Pred(A, \{B \mid P\}) \Rightarrow P'\) if \(A \Rightarrow A', B \Rightarrow B', P \Rightarrow P'\)
- \(\Pred(A, B) \Rightarrow \Pred(A', B')\) if ...
- \(\Pred(A, \{B \mid P\})^* = P^*\) 

あと、 \(\Take\) も束縛が発生しないようにするには \(\Take f\) のようにするが、
redux みたいな部分は増えないのでやることは特に増えない。

### ちゃんと全部書いておく
#### 代入順序の交換について
\(M[x := L][y := N[x := L]] = M[y := N][x := L]\) が成り立つ。
（ただし、束縛変数に関する条件があるので注意）
証明はしないでいいか。

#### parallel reduction
base case
- \(s \Rightarrow s\)
- \(x^s \Rightarrow x^s\)
cong case
- \((x^s: A) \to B \Rightarrow (x^s: A') \to B'\) if \(A \Rightarrow A', B \Rightarrow B'\)
- \(\lambda x^s: A. B \Rightarrow \lambda x^s:A'. B'\) if \(A \Rightarrow A', B \Rightarrow B'\)
- \(A B \Rightarrow A' B'\) if \(A \Rightarrow A', B \Rightarrow B'\)
- \((\lambda x^s: A. M) B \Rightarrow M'[x := B']\) if \(A \Rightarrow A', B \Rightarrow B', B \Rightarrow M'\)
- \(\{x: A \mid P\} \Rightarrow \{x: A' \mid P'\}\) if \(A \Rightarrow A', P \Rightarrow P'\)
- \(\Power A \Rightarrow \Power A'\) if \(A \Rightarrow A'\)
- \(\Pred(A, B) \Rightarrow \Pred(A', B')\) if \(A \Rightarrow A', B \Rightarrow B'\)
- \(a =_A b \Rightarrow a' =_{A'} b'\) if \(A \Rightarrow A', a \Rightarrow a', b \Rightarrow b'\)
- \(\Take x: A. B \Rightarrow \Take x: A'. B'\) if \(A \Rightarrow A', B \Rightarrow B'\) 
- \(\Take f \Rightarrow \Take f'\) if \(f \Rightarrow f'\)
- \(\exists A \Rightarrow \exists A'\) if \(A \Rightarrow A'\)
redux case
- \(\Pred(A, \{x: B \mid P\}) \Rightarrow \lambda x: B'. P'\) if \(A \Rightarrow A', B \Rightarrow B', P \Rightarrow P'\)
- \(\Proof P \Rightarrow \Proof P'\) if \(P \Rightarrow P'\)

Remark: beta reduction はここから次のように制限したものになる。
- \(s \Rightarrow s\) と \(x^s \rightarrow x^s\) を抜く
- sub term はそれぞれ一つだけ reduction を進める
  - 例： \((x^s: A) \to B \to_\beta (x^s: A') \to B\) みたいに、 \(A\) が進んだときは \(B\) を進めない。
- \((\lambda x^s: A. M) B \to_\beta B[x := A]\) のような redux は subterm を進めない。
  - \(\Pred(A, \{x: B \mid P\}) \to_\beta \lambda x: B. P\) もそう。
  - \(\Pred(A, \{B \mid P\}) \to_\beta P\) もそう。

###### \(M \Rightarrow M\)
base case と congruent なやつを使えば、 \(M\) の構造についての帰納法でよい。

###### \(M \to_\beta N\) なら \(M \Rightarrow N\)
\(\to_\beta\) の構成に関する帰納法でよい。
このさいに \(M \Rightarrow M\) が必要になる。
\(\to_\beta\) も congruent に定義しているところでは、そのまま次のような議論が使える。
- \(M N \to_\beta M' N\) で \(M \to_\beta M'\) のとき、帰納法の仮定から \(M \Rightarrow M'\) が得られて、 \(N \Rightarrow N\) と合わせて par.red ができる。

そうじゃない、 redux っぽいところはこれも対応する par.red を考えればいい。
- \((\lambda x^s: A. M) B \to_\beta M [x := B]\) のとき、 \(M \Rightarrow M, B \Rightarrow B, A \Rightarrow A\) から、これと par.red ができる。
- \(\Pred(A, \{x: B \mid P\}) \to_\beta \lambda x:B. P \) のときは、これも上と同様。
- \(\Pred(A, \{B \mid P\}) \to_\beta P\) のときも同様。

###### \(M \Rightarrow N\) なら \(M \to_\beta^* N\)
\(M \Rightarrow N\) の構成に関する帰納法でよい。
- base case に対しては、 \(\to_\beta^*\) は reflective + transitive な閉包なので、 reflective の方からわかる。
- cong case に対しては、帰納法の仮定から楽にできる。
  - 例： \(M N \Rightarrow M' N'\) if \(M \Rightarrow M', N \Rightarrow N'\) に対しては、帰納法の仮定から \(M \to_\beta^* M', N \to_\beta N'\) が得られていて、 \(\to_\beta\) の cong の方を適用すればいい。
- redux case に対しては、これも redux + 帰納法の仮定からわかる。
  - 例：\((\lambda x^s: A. M) B \Rightarrow M'[x := B']\) if \(A \Rightarrow A', B \Rightarrow B', M \Rightarrow M'\) のとき：
  帰納法の仮定から、 \(A \to_\beta^* A', B \to_\beta^* B', M \to_\beta M'\) が得られている。よって、 \((\lambda x^s: A. M) B \to_\beta^* \lambda (x^s: A'. M') B' \to_\beta M'[x := B']\) になる。

他は全部同じようにできる。

###### \(M \Rightarrow M', N \Rightarrow N'\) なら \(M[x: = N] \Rightarrow M'[x: = N']\)
binding を行うような項（ \((x^s: A) \to B\), \(\lambda x: A. B\), \(\{x: A \mid P\}\), \(\Take x: A. B\) ）は、α同値で代入する変数とかぶらないようにしておく。
（もっと強く、 \(\text{BV}(M)\) が \(\text{FV}(M)\) や \(\text{FV}(N)\) とかぶらないようにしておいてもいい。）

\(M \Rightarrow M'\) の構成に関する帰納法でよい。
base case
- \(s \Rightarrow s\) に対しては代入で何も変わらないから。
- \(x^s \Rightarrow x^s\) に対しては、 \(N \Rightarrow N'\) になるか \(x^s \Rightarrow x^s\) になるか。
cong case:binding に関する仮定を考えると（考えなくても \(M \Rightarrow M\) があるのであまり変わらないけれど）代入が cong に進むだけなので、帰納法の仮定と合わせればよい。
- \((\lambda y^s: A. B)[x := N] \equiv \lambda y^s: A[x := N]. B[x := N] \Rightarrow \lambda y^s: A'[x := N']. B'[x := N'] \equiv (\lambda y^s: A'. B')[x := N']\)
redux case: この場合、代入の順序の入れ替えに関する補題を用いる必要がある。
- \(((\lambda y^s: A. M) B) \Rightarrow M'[y := B']\) if \(A \Rightarrow A', M \Rightarrow M', B \Rightarrow B'\) に対して、
  帰納法の仮定から \(M[x := N] \Rightarrow M'[x := N'], B[x := N] \Rightarrow B'[x := N']\) が得られている。
  示したいのは次のもの。
  \[ ((\lambda y^s: A. M) B)[x := N] \Rightarrow (M'[y^s := B'])[x := N'] \]
  ここで、 \(((\lambda y^s: A. M) B)[x := N] \equiv (\lambda y^s: A[x := N]. M[x := N]) B[x := N] \Rightarrow (M'[x := N'])[y := B'[x := N']] \equiv M'[y := B'][x := N']\) である。（ここで束縛の仮定を用いることになる。）
- \(\Pred(A, \{y: B \mid P\}) \Rightarrow \lambda y^{*^s}:B'. P'\) のとき。帰納法の仮定から \(B[x := N] \Rightarrow B'[x := N']\) と \(P[x := N] \Rightarrow P'[x := N']\) が得られている。なので、 \(\Pred()[x := N] = \Pred(A, \{y \mid B[] \mid P[]\}) \Rightarrow \lambda y: B'[]. P'[]\) からわかる。
- \(\Pred(A, \{B \mid P\}) \Rightarrow P'\) の場合も同様。

#### \(M^*\) を作る
base case
- \(s^* = s\)
- \(x^* = x\)
redux case
- \(((\lambda x: A. M) B)^* = M^*[x := B^*]\)
- \(\Pred(A, \{x: B \mid P\})^* = \lambda x: B^*. P^*\)
cong case
- \((M N)^* = M^* N^*\) if \(M \not \equiv \lambda x: A. B\)
- \(\Pred(A, B)^* = \Pred(A^*, B^*)\) if \(B \not \equiv \{x: C \mid P\}\)
- \(((x: A) \to B)^* = (x: A^*) \to B^*\)
- ...

###### \(M \Rightarrow N\) なら \(N \Rightarrow M^*\)
\(M\) の構造に関する帰納法を用いる。
（\(M\) の構造を見ることで \(M \Rightarrow N\) が何でえられているか制限できることに注意）
- \(M \equiv x, s\) の場合、 \(M \Rightarrow N\) は base case でしか与えられない。なので、 \(N \equiv M\) であるから、 \(M^* \equiv M\) と合わせて成り立つ。
- \(M\) が redux の形にならない場合、 \(M \Rightarrow N\) は cong case でしか与えられない。この場合には帰納法の仮定を用いることで証明できる。
  - 例： \(M \equiv (x: A) \to B\) のときには \(N \equiv (x: A' \to B')\) で \(A \Rightarrow A', B \Rightarrow B'\) であることがわかる。
    このとき、帰納法の仮定から、 \(A \Rightarrow A' \Rightarrow A^*, B \Rightarrow B' \Rightarrow B^*\) が得られているので、 \((x: A') \to B' \Rightarrow (x: A^*) \to B^*\) である。
- \(M\) が redux の形になっている場合、 \(M \Rightarrow N\) の構成に使ったルールは複数ありうるので、場合分けする。
  - \(M \equiv (\lambda x: A. M) B\) のとき。
    - \(N \equiv (\lambda x: A'. M') B'\) で cong なときには、帰納法の仮定から \(M \Rightarrow M' \Rightarrow M^*\) などが成り立っている。
      この場合には、 \((\lambda x: A'. M') B' \Rightarrow M^*[x := B^*]\) が使える。
    - \(N \equiv M'[x := B']\) で \(M \Rightarrow M', B \Rightarrow B'\) のときには帰納法の仮定と補題を用いて、 \(M'[x := B'] \Rightarrow M^*[x := B^*]\) がわかる。
  - \(M \equiv \Pred(A, \{x: B \mid P\})\) のとき。
    - \(N \equiv \lambda x: B'. P'\) のときには帰納法の仮定から \(B' \Rightarrow B^*\) と \(P' \Rightarrow P^*\) が得られているので、 \(\lambda x: B'. P' \Rightarrow \lambda x: B^*. P^*\) である。
    - \(N \equiv \Pred(A', \{x: B' \mid P'\})\) のときには帰納法の仮定から \(B' \Rightarrow B^*\) などが得られているので \(\Pred(A', \{x: B' \mid P'\}) \Rightarrow \lambda x: B^*. P^*\) である。
  - \(M \equiv \Pred(A, \{B \mid P\})\) のときは議論が同じ。

###### confluence
\(M \Rightarrow M_1, M_2\) でも \(M_1, M_2 \Rightarrow M^*\) がわかるので、 \(\Rightarrow\) は合流性があるから、これに挟まれている \(\to_\beta\) も合流性がある。
