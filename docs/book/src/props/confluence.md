# Core calculus の合流性

適用する構文と PTS への移送義務は、[証明の適用範囲](props.md)による。

対象は [分類付き補助体系](sorted-calculus.md) の、一般の datatype 宣言を除いた体系である。
Box を含む体系を \(\mathcal S_\Box\)、Box 関係の構文・規則を除いた体系を
\(\mathcal S_0\) と書く。判断は有限導出によって生成する。
ここで示すのは補助 reduction の合流性である。元の reduction の合流性や subject reduction は結論しない。
代入の合成則は[構文的補題](metatheory.md#substitution)を使う。
以下の本文は分類付き補助体系の Set/Prop の三構文に適用する。
式中で省略した \(\Pi,\lambda,@,\operatorname{stepMatch}\) の rule label・sort 添字は固定し、
全 congruence rule はそれらを保持する。
beta の lambda と application は同じ \(r\) を持つ場合にだけ root とする。
Pred の reduct は \(p_i\)、step match の branch application は \(h_{i,\sigma}\)、
run の application は \(s^{i,i}\) を持つ。
補助規則で外すのは、下に明記する constructor の型引数の一致条件だけである。

<a id="auxiliary-reduction"></a>

## Box-free raw conversion の共通簡約先

\(\to_0\) を Box-free core の raw reduction とする。
`stepMatch` と `runCase` の左辺では、同じ型添字が複数回現れる。
そのため、この規則をそのまま left-linear と呼ぶことはできない。

補助 reduction \(\rightsquigarrow\) を次のように定義する。
beta、Pred、run の規則は \(\to_0\) と同じとし、次の四規則では
内側と外側の型添字の一致を要求しない。

\[
\begin{aligned}
\operatorname{stepMatch}_{A,B}(x^s.P,c,d)@\operatorname{continue}_{C,D}(a)&\rightsquigarrow c@a,\\
\operatorname{stepMatch}_{A,B}(x^s.P,c,d)@\operatorname{finish}_{C,D}(b)&\rightsquigarrow d@b,\\
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
(\operatorname{stepMatch}_{A,B}(x^s.P,c,d)@\operatorname{continue}_{C,D}(a))^\star&=c^\star @a^\star,\\
(\operatorname{stepMatch}_{A,B}(x^s.P,c,d)@\operatorname{finish}_{C,D}(b))^\star&=d^\star @b^\star,\\
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
- step match、run、runCase の root の場合は、右辺の各引数を帰納法で簡約する。
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


## Transport の parallel reduction

transport の parallel reduction は \(A\)、\(a\)、\(b\)、\(B\)、\(u\) を同時に簡約する congruence であり、\(B\) は \(x\) の下で扱う。
complete development も同じ constructor を保って五引数に再帰する。
parallel-subst では \(x\) を新鮮にして \(B\) へ帰納法を適用し、他の引数へ通常の帰納法を適用する。
complete development の補題は五引数の帰納法の結果に congruence を適用することで得る。
transport に root reduction はないので既存の root と重なる場合は増えず、補助関係の diamond と aux-join は保存される。
