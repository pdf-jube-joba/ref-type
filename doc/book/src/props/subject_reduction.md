# 補助体系の subject reduction

対象は [generation](generation.md#auxiliary-system) で定義した
\(\mathcal S_+\) と補助 reduction \(\rightsquigarrow\) である。
以下のすべての conversion は \(\equiv_+\) を使う。
元の体系 \(\mathcal S_0\) の SR を結論するものではないが、
\(\mathcal S_0\subseteq\mathcal S_+\) なので、無矛盾性の証明を
\(\mathcal S_+\) で進めるために使える。

## 利用する補題と帰納法の順序

先に得ているのは、raw な補助 reduction の合流性、
[generation](generation.md#generation)、Substitution、Regularity、
Context-conversion、Prop-conversion である。どれも SR と集合モデルを使わない。

以下では、まず principal でない constructor に対する root の保存を示す。
次に typing・kind formation・provability の導出に関する同時帰納法で、
compatible position と subject を保つ規則を扱う。
provability の場合にも帰納法を用いるのは、proof term の唯一の premise が
provability であり、その導出を真部分木として扱う必要があるためである。

<a id="root-preservation"></a>

## 一般の constructor typing に対する root の保存

ここでは、最後の規則がその root に対応する消去規則の場合を扱う。
constructor の typing は、subset や conversion を何段経由していてもよい。

### Beta

dep elim の premise を
\[
\Gamma\vdash_+A:\sigma_1,\quad
\Gamma,x:A\vdash_+B:\sigma_2,\quad
\Gamma\vdash_+\lambda_r x:C.m:\Pi_r x:A.B,\quad
\Gamma\vdash_+a:A
\]
とする。generation により
\(\Gamma,x:C\vdash_+m:D\)、\(C\equiv_+A\)、\(D\equiv_+B\) と
C、D の formation を得る。
conversion により \(a:C\)、Substitution により
\[
\Gamma\vdash_+m[x:=a]:D[x:=a].
\]
両結果型はそれぞれの formation と Substitution から形成でき、
\(D[x:=a]\equiv_+B[x:=a]\) なので、もう一度 conversion を使う。
これで元の結果型 \(B[x:=a]\) における reduct の typing を得る。

### Pred/subset

predicate の premise は
\(\{x:C\mid P\}:\Power A\)、\(t:A\) と A の formation を含む。
generation から \(C\equiv_+A\)、C の formation、
\(\Gamma,x:C\vdash_+P:*^p\) を得る。
従って \(t:C\) に conversion でき、
\[
\Gamma\vdash_+(\lambda_{p_i}x:C.P)@_{p_i}t:*^p
\]
を dep intro/elim で構成できる。
外側と内側の domain が構文的に一致するという仮定は要らない。

### prec/continue と prec/finish

外側の型を \(\operatorname{RunStep}(A,B)\)、内側の constructor の型添字を C、D とする。
continue の場合、generation により \(C\equiv_+A\)、\(D\equiv_+B\)、
\(a:C\) を得る。conversion で \(a:A\) とし、branch c に dep elim を適用すると
\[
\Gamma\vdash_+c@_{h_{i,\sigma}}a:
 P[x:=\operatorname{continue}_{A,B}(a)].
\]
一方、元の prec の結果型は \(P[x:=\operatorname{continue}_{C,D}(a)]\)。
二つの continue は型添字の compatible conversion で同値である。
両結果型の formation は motive の formation と Substitution から得られるので、
conversion で元の結果型に戻せる。
finish は \(b:D\) を \(b:B\) に移し、branch d を使う同じ構成である。

### run と runCase

run の unfold では \(f@_{s^{i,i}}a:\operatorname{RunStep}(A,B)\) を形成し、
id intro によりその自己等号を得る。元の Acc premise と合わせて runCase を適用する。

runCase/continue では、generation により内側の
\(\operatorname{continue}_{C,D}(b)\) の引数を \(b:A\) に型付けできる。
型添字の conversion と Prop-conversion により、元の equality premise を
\[
\Gamma\vDash_+f@_{s^{i,i}}a=\operatorname{continue}_{A,B}(b)
\]
へ移す。移した命題は、両辺を \(\operatorname{RunStep}(A,B)\) で型付けして形成できる。
acc descent により \(\operatorname{Acc}_{A,B}(f,b)\)、run により
\(\operatorname{run}_{A,B}(f,b):B\) を得る。

runCase/finish では、generation により \(b:D\) と \(D\equiv_+B\) を得る。
conversion で \(b:B\) とすれば、それが reduct の typing である。

ここまでの構成に SR の仮定はない。

<a id="sr-plus"></a>

## Compatible closure を含む保存

**定理。**
\[
\begin{aligned}
\Gamma\vdash_+e:T,\quad e\rightsquigarrow e'
 &\Longrightarrow\Gamma\vdash_+e':T,\\
\Gamma\vdash_+K:\kappa(b),\quad K\rightsquigarrow K'
 &\Longrightarrow\Gamma\vdash_+K':\kappa(b),\\
\Gamma\vDash_+P,\quad P\rightsquigarrow P'
 &\Longrightarrow\Gamma\vDash_+P'.
\end{aligned}
\tag{SR-plus}
\]
family と rule label は保存され、context は固定したままである。

**証明。** 型演算子 typing、項 typing、kind formation、provability の有限導出について
同時帰納する。
帰納法を呼ぶのは、元の導出に明示された真部分木だけである。

### Subject を保つ規則

- conversion：subject の typing の premise に帰納法を使い、元の conversion を再適用する。
- weak と provable weak：元の premise に帰納法を使って weakening する。
  raw reduction は自由変数を増やさないので freshness は保存される。
- subset weak：subject の typing の premise に帰納法を使って同じ規則を適用する。
- subset intro：\(e:A\) に帰納法を使って \(e':A\) を得る。
  新しい \(\Pred(A,S,e')\) は predicate 規則で形成でき、
  \(\Pred(A,S,e)\equiv_+\Pred(A,S,e')\)。
  元の provability を Prop-conversion で移し、subset intro を適用する。

最後の操作は、provability の導出に SR を先取りして適用するものではない。
元の証明と、新しい命題の明示的な formation から Prop-conversion を適用している。

### 基本 constructor と binder

variable と base kind には簡約がない。root の場合は上の構成を使う。
積・lambda の domain \(A\rightsquigarrow A'\) では、
domain の formation premise に帰納法を使って A' を形成する。
Context-conversion で binder 内の全 premise を \(x:A'\) の context へ移す。
body 自身を簡約する場合は、その body の premise に帰納法を使う。
dep form/intro を再適用し、lambda の結果型が変わった場合は
形成済みの二つの product の conversion で元の型へ戻す。

application の function または argument を簡約する場合は、
対応する typing premise に帰納法を使って dep elim を再適用する。
argument が \(a'\) になった場合の結果型 \(B[x:=a']\) は
Substitution で形成され、元の \(B[x:=a]\) と同値なので conversion できる。
型演算子の lambda/application も同じ議論である。

proof term では、provability の premise に帰納法を使って
\(\Gamma\vDash_+P'\) を得る。
\(\Proof P':P'\) を構成し、Regularity で得る P と P' の formation を用いて P へ conversion する。

### Set/Prop の引数位置

一つの引数の一歩簡約に対して、以下の順で規則を再構成する。

1. 簡約する型・項・motive の明示的な premise に帰納法を使う。
2. 型注釈が変わる場合、その新しい formation を作り、
   変更しない項の typing を新しい表示型へ conversion する。
   binder の context には Context-conversion を使う。
3. 必要な新しい命題を formation 規則で形成する。
   元の命題と新しい命題は compatible conversion と代入の可換性で同値なので、
   元の provability を Prop-conversion で移す。
4. 同じ constructor の規則を適用する。結果型が変わった場合は、
   両方の formation と compatible conversion により元の型へ戻す。

この手順で必要になる formation と移送先は次のとおりである。

| 規則 | 再構成する formation・premise |
| --- | --- |
| Power、Ty、Pred | 新しい A の formation、S の Power 型での typing、t の A での typing |
| subset form | 新しい domain の context における predicate の formation |
| id form、exists form | 新しい共通型での両辺の typing、または新しい対象型の formation |
| take elim set | 新しい \(X\to T\) での f の typing、\(\exists X\)、二重の積で表した定値性 |
| take elim prop | 新しい \(X\to P\) での g の typing、\(\exists X\) |
| RunStep と constructor | 新しい A、B の formation、および constructor の引数 typing |
| prec | 新しい RunStep の context での motive、代入後の二つの branch 型、両 branch の typing |
| Acc、run、runCase | 新しい \(A\to\operatorname{RunStep}(A,B)\) での f の typing、状態と step の typing、Acc と equality |

例えば take の定値性の新しい命題は、拡張 context の二変数に f を適用し、
id form と dep form を二回使って形成する。非空性は exists form で形成する。
prec の新しい branch 型は、motive の formation に新しい constructor を
Substitution し、dep form で量化すれば形成できる。
runCase の新しい equality は、新しい共通 RunStep 型で両辺を型付けして形成する。
従って第三段で新しい命題の formation を仮定していない。

重複していた内外の型添字の一方だけを簡約した場合も、
その変更位置を一つの引数としてこの手順で扱える。
内外の添字を同時に簡約するという仮定は不要である。

### Provability

provable の場合は、明示された \(P:*^p\) の premise に帰納法を使う。
元の proof term の typing を P' へ conversion して provable を再適用する。
残りの規則では新しい結論 P' の formation を構成し、
元の結論の証明に Prop-conversion を適用する。
その formation の構成を以下に列挙する。

- subset prop：compatible position は明示された A、S、t の typing に帰納法を使う。
  Pred/subset root なら、上の Pred/subset の構成を用いる。
- id intro：簡約された側の項の typing に帰納法を使い、
  変更しない側と同じ型で id form を適用する。
- id elim：結論の beta root では、明示された P の formation と b の typing に
  Substitution を使う。compatible position では A、P、b の該当する premise に
  帰納法を使い、必要な context conversion と dep intro/elim で形成する。
- exists intro：対象型の formation に帰納法を使い、exists form を適用する。
- take equal：左辺の簡約には、明示された Take の typing premise への帰納法を使う。
  右辺 \(f@t\) の compatible step は f または t の premise への帰納法と dep elim。
  右辺の beta root は上の一般の beta の構成を使う。
  いずれの場合も両辺を元の T で型付けでき、id form を適用できる。
- acc intro/descent：結論に出現する A、B、f、状態の該当する typing premise に
  帰納法を使い、新しい表示型へ conversion して acc form を適用する。

provable weak は既に扱った。これで全規則と全 reduction position を尽くす。□

<a id="typed-join"></a>

## 型付きの共通簡約先

**系。**
\[
\begin{gathered}
\Gamma\vdash_+A:\sigma,\quad\Gamma\vdash_+B:\sigma,\quad A\equiv_+B\\
\Longrightarrow
\exists C.\ A\rightsquigarrow^*C,\ B\rightsquigarrow^*C,\
              \Gamma\vdash_+C:\sigma.
\end{gathered}
\tag{Typed-join-plus}
\]
二つの簡約列のすべての中間項も \(\Gamma\) のもとで \(\sigma\) に型付けできる。

**証明。** raw な補助 reduction の合流性で C と有限列を取る。
各列の長さに関する帰納法で SR-plus を繰り返す。□

これにより \(\mathcal S_+\) では、conversion の両端から
「中間項も型付けできる共通簡約先」までは得られる。
元の conversion のすべての zigzag が型付きになるという主張ではない。

<a id="semantic-step"></a>

## TC までの残り

以下は従来の非コード化解釈についての未解決の主張である。
core の無矛盾性は、別の[型コードモデル](coded_model.md)と
[H-step・導出移送](semantic_conversion.md)で証明するため、この主張を仮定しない。

上の証明は集合モデルを一切使わない。
しかし、型付きの簡約列を得ることと、その各段が集合の解釈を保存することは別である。
次の主張は、このページではまだ証明していない。
\[
\begin{gathered}
\Gamma\vdash_+A:\sigma,\quad A\rightsquigarrow A'\\
\Longrightarrow
\forall\rho\in\operatorname{Val}(\Gamma).\
\llbracket A\rrbracket_\rho=\llbracket A'\rrbracket_\rho.
\end{gathered}
\tag{Semantic-step-plus}
\]

これを健全性を前提にせず証明できれば、Typed-join-plus に沿って解釈を移して
\(\mathrm{TC}_+\) を得る。Core-inclusion により、元の TC もその特殊な場合として従う。
従って、この経路では元の \(\mathcal S_0\) の SR を別途証明する必要はない。

一つの候補は、typing と型付き等号の導出を相互帰納的に定義し、
その健全性と raw conversion との対応を証明する方法である。
通常の PTS については [Siles–Herbelin, Pure Type System conversion is always typable](https://doi.org/10.1017/S0956796812000044)
がこの対応を証明している。しかし本体系の subset・Take・Acc・run は PTS の規則ではないため、
その定理を直接適用して Semantic-step-plus を証明済みとはできない。
