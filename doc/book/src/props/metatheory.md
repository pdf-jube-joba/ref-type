# Core calculus の構文的補題

この文書では [`system.md`](../system.md) の、一般の datatype 宣言を除いた
core を扱う。集合モデル、無矛盾性、subject reduction は仮定しない。
特に、合流性だけから subject reduction が従うとは主張しない。
モデルの構成と未解決の証明義務は [proof.md](proof.md) に記す。

## 1. 束縛と代入

項は alpha 同値で同一視する。変数の sort 注釈は名前の一部とし、
代入 \(t[x^s:=u]\) はその注釈を持つ変数だけを置換する。
lambda、product、subset は表示された変数を body で束縛する。
`prec` の \(x^s.P\) は \(P\) の中だけで \(x^s\) を束縛する。
従って motive への代入はこの局所変数を避ける。
Program の binder は Set の binder と別の名前空間に置く。

以下の式は、\(x\ne y\)、\(y\notin\mathrm{FV}(u)\) のもとで成り立つ。

\[
t[y:=v][x:=u]
=_\alpha t[x:=u][y:=v[x:=u]].
\tag{subst-comp}
\]

**証明。** \(t\) の構造帰納法。変数 \(x\)、変数 \(y\)、その他の変数、
sort の四場合では両辺を代入の定義で展開する。
束縛を持たない constructor では各引数への帰納法の仮定を使う。
束縛 constructor では、その局所変数を \(x,y,u,v\) の自由変数と
異なる名前へ alpha-renaming してから、annotation と body に帰納法を使う。
閉じた Program payload への Set 変数の代入は恒等である。□

同じ証明から、自由変数を capture しない renaming と代入の可換性を得る。

## 2. Box-free raw conversion の共通簡約先

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

### 2.1 Parallel reduction

\(t\Rrightarrow u\) を次の規則で生成する。

1. sort と変数は自分自身へ写る。
2. 各 constructor について、全引数を並列に簡約する congruence rule を置く。
   束縛 body は同じ局所変数のもとで簡約する。
3. beta は
   \[
   (\lambda x:A.m)@a\Rrightarrow m'[x:=a']
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

### 2.2 Complete development

\(t^\star\) を構造再帰で定義する。root に一致するときは以下を優先する。

\[
\begin{aligned}
((\lambda x:A.m)@a)^\star&=m^\star[x:=a^\star],\\
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

### 2.3 Head discrimination と injectivity

sort、変数、Power、Ty、product、RunStep は、
\(\rightsquigarrow\) によって自分の外側の constructor を失わない。
従って `aux-join` から以下が従う。

- 異なる sort 定数は \(\equiv_0\) でない。
- 自由変数は sort、Ty、Power、product、RunStep と \(\equiv_0\) でない。
- Ty、Power、product、RunStep の異なる head 同士は \(\equiv_0\) でない。
- \(\Power A\equiv_0\Power B\) なら \(A,B\) は補助関係で共通簡約先を持つ。
- 二つの product が \(\equiv_0\) なら、binder の sort 注釈は一致し、
  alpha-renaming 後の domain 同士、body 同士はそれぞれ補助関係で共通簡約先を持つ。

最後の二項について、ここで得た引数の join を直ちに
\(A\equiv_0B\) 等へ戻すことはできない。
補助 step の original conversion への可換性は別途必要である。
この区別は subject reduction の証明における循環を避けるために重要である。
