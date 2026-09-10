# Conversion の意味保存と core の無矛盾性

このページでは[型コードモデル](coded_model.md)を使い、raw conversion を含む
現行 core の相対無矛盾性を示す。datatype は含めない。
従来の集合そのものによる候補解釈の TC は使わず、それを証明したとも主張しない。

証明の順序は次のとおりである。

1. 意味が等しい型の間だけ conversion する補助体系を定義し、導出帰納法で健全性を示す。
2. その補助体系で generation、簡約の型保存と意味保存を示す。
3. 合流性を使い、元の raw conversion を含む導出を補助体系へ移す。
4. 空の命題を解釈し、既存の Box 消去を適用する。

第一段の conversion は意味保存を側条件に持つが、元の体系にその側条件を追加するのではない。
第三段で、元の全導出がその側条件を満たすことを証明する。

## 消去後の reduction

\(\epsilon\) は[証明項の消去](coded_model.md)とする。
消去構文上の \(\leadsto\) は、[補助 reduction](confluence.md#auxiliary-reduction)のうち
結果が proof family でない root 規則と、その compatible closure で生成する。
消去によって失われた proof の内部位置には簡約を設けない。
したがって \(\bullet\) に簡約はない。
prec/runCase の内外の型添字の一致を要求しないことは、補助 reduction と同じである。

**補題。**
\[
e\rightsquigarrow e'\Longrightarrow
\epsilon(e)\leadsto^{\leq1}\epsilon(e'),\qquad
e\equiv_+e'\Longrightarrow\epsilon(e)\equiv_\epsilon\epsilon(e').
\tag{Erase-reduction}
\]
\(\equiv_\epsilon\) は \(\leadsto\) の同値閉包である。
proof 内の step と proof を返す root は両辺とも \(\bullet\)。
それ以外の root は Erase-substitution により対応する root になり、compatible step は構文帰納法による。

**補題。** \(\leadsto\) は合流する。

**証明。** [補助 reduction の平行簡約と complete development](confluence.md)の構成を
消去構文に適用する。\(\bullet\) の development は \(\bullet\)。
残る root は beta、Pred/subset、非 proof の prec、run、runCase であり、
root と compatible step の重なりは元の証明と同じである。
Pred に対する二つの平行規則と代入補題も残る。
proof variable の代入は恒等操作なので、その場合の代入補題は等式になる。
これ以外に新しい root や重なりはない。
従って平行簡約の diamond とその反復による合流性が得られる。□

## 意味的 conversion を持つ補助体系

\(\mathcal H\) の構文は消去構文、規則は \(\mathcal S_+\) の非 conversion 規則を
\(\epsilon\) で写したものとする。
例えば proof の variable、dep intro、dep elim、proof term、take elim prop、proof を返す prec の
結論の subject はすべて \(\bullet\) である。それぞれの premise は保持する。
\(\bullet:P\) を無条件に認める規則はない。

conversion だけは次に置き換える。
\[
\frac{\Gamma\vdash_H e:A\qquad\Gamma\vdash_H A:\sigma\qquad
       \Gamma\vdash_H B:\sigma\qquad A\simeq_\Gamma B}
     {\Gamma\vdash_H e:B},
\quad
A\simeq_\Gamma B\ :\Longleftrightarrow\
\forall\rho\in\operatorname{Val}_c(\Gamma).\
\langle A\rangle_\rho=\langle B\rangle_\rho.
\tag{H-conversion}
\]
意味の等しさは decoding の等しさだけではなく、解釈したコードそのものの等しさである。
命題の場合は真理値の等しさになる。
Val と解釈は既に raw 構文について定義済みなので、この側条件は typing に依存して定義されない。
\(\mathcal H\) の導出も有限木である。

### H の健全性

**補題。** \(\mathcal H\) の全規則は型コードモデルについて健全である。
すなわち、各 \(\rho\in\operatorname{Val}_c(\Gamma)\) について
\[
\begin{aligned}
\Gamma\vdash_H e:T\ (e\in\mathsf E_\sigma)
 &\Longrightarrow \langle e\rangle_\rho\in|T|_{\sigma,\rho},\\
\Gamma\vdash_H K:\square^s_i
 &\Longrightarrow \langle K\rangle_\rho\in\mathcal C_{i+1},\\
\Gamma\vdash_H K:\square^p
 &\Longrightarrow \langle K\rangle_\rho\in\mathcal C_\omega,\\
\Gamma\vDash_H P&\Longrightarrow\langle P\rangle_\rho=1.
\end{aligned}
\tag{H-soundness}
\]

**証明。** 全判断の導出に関する同時帰納法。
Set の literal Take に対しては、さらに
\[
\operatorname{El}(\langle X\rangle_\rho)\ne\varnothing,\qquad
\exists y.\ \forall x\in\operatorname{El}(\langle X\rangle_\rho).
\operatorname{app}(\langle f\rangle_\rho,x)=y
\tag{H-K}
\]
を帰納命題に加える。[従来の健全性](soundness.md)の K と同じ有限の導入追跡を使う。

- axiom は \(\mathsf u_i\in\mathcal C_{i+1}\)、\(\mathsf p\in\mathcal C_\omega\)。
  variable、start、weak は Val の定義。proof variable の値は、valid valuation では 0 である。
- conversion は側条件により classifier の値、従って decoding を変えない。
  この場合に raw conversion の意味保存は使用しない。
- dep form は型コードモデルの universe 表。
  非 proof の dep intro/elim は decoding の Prod と Trace、Coded-substitution。
  proof の dep intro は、domain の全要素で body の真理値が 1 なので product が 1。
  proof の dep elim は product の真理値 1 と argument の所属から対象 fiber が 1 となる。
  どちらの結論も \(\bullet\) の値 \(0\in1\) である。
- provable は \(0\in\langle P\rangle_\rho\in\mathbb B\) から真理値 1。
  proof term はその逆方向。
- Power と Ty は pow/ref の validity、subset form は separation。
  subset intro/weak/prop は \(\operatorname{El}(\mathsf{ref}(c,S))=S\subseteq\operatorname{El}(c)\)。
- id form/intro は集合の等号。id elim は同じ集合値を valuation に代入するため真理値を保つ。
  predicate application の beta 則には、premise の argument 所属と Trace を使う。
- exists は decoding の非空性。take elim set は非空な domain と定値性から H-K を得て、
  union がその一定値に等しいことを使う。take equal は明示された Take typing の H-K を使う。
  take elim prop は非空な domain の全 fiber が P なので P が真となる。
- RunStep は sum の validity、constructor は tagged sum の所属。
  非 proof の prec は対応する branch の Prod の所属、proof の prec は対応する fiber の真理値 1。
  どちらも motive の代入は Coded-substitution で結論の型に一致する。
- Acc の導入・下降、run、runCase は decoding した A、B に対する
  [Run-laws](model.md#termination)。f の全域性、argument の所属、Acc と equality はそれぞれ premise の帰納法による。

H-K は take elim set で作られ、weak、conversion、subset intro/weak では
同じ subject の真部分木から保たれる。他の規則は literal Take を結論しない。
以上は簡約、合流性、元の体系の健全性を使わない導出帰納法である。□

### 構造補題

\(\mathcal H\) で weakening、Substitution、Regularity、Context-conversion が成り立つ。
Context-conversion では、形成された宣言型の \(A\simeq_\Gamma B\) を仮定する。
Prop-conversion は、\(P\simeq_\Gamma Q\)、P、Q の formation と P の provability から Q の provability を与える。

**証明。** [typing](typing.md)の導出帰納法を使う。
意味的 conversion に固有の確認は次の三つである。
weakening では valid valuation を prefix へ制限する。
context conversion では等しい classifier は同じ decoding を持つので、変更前後の Val が一致する。
代入では H-soundness から、代入項の値を追加した valuation が元の context に valid である。
Coded-substitution により、元の側条件を代入後の側条件へ移せる。
残りの constructor は従来と同じ再構成である。
Regularity と Prop-conversion も通常の導出構成であり、SR は使わない。□

## H における意味的 generation

**補題。** 消去後に残る literal lambda を
\(\Gamma\vdash_H\lambda_r x:C.m:\Pi_r x:A.B\) と型付けできるなら、
導入時の body type D と全導入 premise を回収でき、さらに
\[
C\simeq_\Gamma A,\qquad D\simeq_{\Gamma,x:C}B.
\tag{H-lambda-generation}
\]
第二式で B は Context-conversion によって形成できる。
literal subset の Power 型、continue/finish の RunStep 型についても、
内外の型注釈が \(\simeq_\Gamma\) であることと導入 premise を回収できる。

**証明。** [generation](generation.md)の有限の導入追跡と同じく、
subject を保つ weak、conversion、subset intro/weak を遡る。
消去後に残る literal constructor を作る規則は、対応する導入規則だけである。
proof の各規則の subject は \(\bullet\) なので混同しない。
導入 premise を最終 context へ weakening する。

次に \(\rho\in\operatorname{Val}_c(\Gamma)\) を固定する。
意味的 conversion は型コードを変えず、subset intro/weak は
\(\mathsf{ref}(c,S)\) と c の間を移動する。
ref の parent をたどると rank が真に減るため、必ず一意な非 ref コードに着く。
その終点はこの有限の追跡で不変である。
導入型と表示型はともに pi、pow、sum のいずれかであり、それ自体が終点なので、両コードは等しい。

lambda の場合、pi の injectivity により domain コードが等しく、格納した通常の関数も等しい。
\(\delta_{\sigma_1}\) は固定 sort ごとに単射なので C と A の解釈が等しい。
domain の各要素 a における fiber コードも等しいため、D と B は
\(\Gamma,x:C\) の全 valid valuation で等しい。
他の constructor は pow と sum の injectivity を使う。
valid valuation が存在しない場合、これらの意味的等式は空虚に成立する。□

この証明で、命題の product の injectivity を使っていない点が重要である。
proof を返す lambda は消去されており、残る lambda の関数型は pi コードを持つ。

## H の一歩保存

**定理。** typing または kind formation の判断について
\[
\Gamma\vdash_H e:T,\quad e\leadsto e'
\Longrightarrow
\Gamma\vdash_H e':T,\quad
\forall\rho\in\operatorname{Val}_c(\Gamma).
\ \langle e\rangle_\rho=\langle e'\rangle_\rho.
\tag{H-step}
\]

**証明。** 元の typing・kind formation 導出の高さに関する同時帰納法。
二つの結論を一緒に示す。帰納法を使うのは明示された typing/formation の真部分木だけである。
H-soundness と構造補題は既に独立に証明済みなので、自由に使える。

### Root

最後の規則が対応する消去規則の場合をまず扱う。

- beta：H-lambda-generation で C、D の導入 premise と C と A の意味的等式を得る。
  argument を C へ H-conversion し、Substitution で \(m[x:=a]:D[x:=a]\)。
  fiber の等式と Coded-substitution により \(D[x:=a]\simeq_\Gamma B[x:=a]\) なので結果型を移す。
  意味保存には、H-soundness で得た \(\langle a\rangle_\rho\in|C|_{\sigma_1,\rho}\) と
  Trace、Coded-substitution を使う。
- Pred/subset：generation により内側 domain C と外側 A のコードが等しい。
  argument を C に移して、型演算子 lambda とその application を形成する。
  その argument は El(C) に属するので、subset の membership と predicate body の真理値が一致する。
- prec/continue、prec/finish：generation で constructor argument を外側の A または B へ移す。
  branch に dep elim を適用する。
  内外の型注釈が異なっていても constructor の値は同じ tagged pair なので、
  motive への代入後の結果型は Coded-substitution により意味的に等しい。
  両結果型を形成して H-conversion する。prec の値は定義からその branch application の値である。
- run：f@a の typing と自己等号を作り、元の Acc premise と合わせて runCase を型付けする。
  H-soundness で f の全域性と Acc の意味を得て、Run-laws の unfolding を使う。
- runCase/continue：generation で後続状態 b を A に移す。
  constructor の値は注釈によらないため、元の equality premise を外側の注釈へ Prop-conversion できる。
  acc descent と run で reduct を型付けする。
  Case の定義から値は Run(f,b) に等しい。
- runCase/finish：generation で b を外側の B に移す。Case の定義から値は b。

### Subject を保つ規則

conversion と weak では subject の premise に帰納法を適用して同じ規則を戻す。
subset weak も同様。
subset intro では \(e:A\) の帰納法で \(e':A\) と値の等しさを得る。
新しい Pred を形成し、値が等しいことから元の Pred の証明を Prop-conversion して導入を戻す。
これらは subject の意味を変えない。

### Compatible position

該当する引数または body の明示された typing/formation premise に帰納法を使う。
新旧の値が等しいので、次の再構成を行える。

| 位置・規則 | 必要な再構成と意味保存 |
| --- | --- |
| product/lambda の domain | domain の値が等しいので binder context の Val が一致する。Context-conversion で body の premise を移す。pi に格納する domain と fiber 関数、または lambda の trace が等しい |
| product/lambda の body | 拡張 context の全 valid valuation で帰納法を使う。各 fiber のコード／値が等しいので、product のコード・真理値、または lambda の trace が等しい |
| application | function/argument の値が等しいので app の値が等しい。argument を変えた結果型は Coded-substitution により等しい |
| Power、Ty、Pred、subset | 引数コード・集合・値の等しさから tuple、membership、separation がそれぞれ等しい。subset の binder は context conversion |
| id、exists | 両辺の値、または対象型のコードが等しいので真理値が等しい |
| Take | domain の decoding と関数値が等しいので union が等しい。新しい関数型、非空性、定値性を形成して意味的 conversion で premise を移す |
| RunStep、continue、finish | 同じ sum コード、または同じ tagged pair。必要な argument typing を移す |
| prec | motive の context と両 branch 型を再形成する。scrutinee と branch の値が等しく、motive は演算の値に使わない |
| Acc、run、runCase | domain/codomain の decoding、f、状態、step の値が等しいので D、Run、Case が等しい。新しい Acc と equality を形成して Prop-conversion する |

変更した型注釈に依存する未変更の premise は、両方の formation と
値の等しさによる H-conversion で移す。
新しい結果型が元の結果型と構文的に異なる場合も、Substitution で両方を形成して同じ操作をする。
Take の定値性は拡張 context の二変数に新しい f を適用して形成できる。
prec の branch 型は新しい constructor を motive に代入して形成できる。
従って、再構成中の formation を未証明の SR に委ねていない。

proof の variable、dep intro/elim、proof term、take elim prop、proof prec の
結論の subject は \(\bullet\) であり、簡約はない。
特に provability premise に対する SR の帰納法は必要ない。
これで typing と kind formation に関する帰納法が閉じる。□

**系。** provability も一歩簡約で保存される。
Regularity で \(P:*^p\) を得て、既に証明した H-step を使うと
\(P':*^p\) と \(P\simeq_\Gamma P'\) を得る。Prop-conversion で結論する。
この順序なので、Regularity で作った大きい導出への帰納法は行っていない。

## Raw conversion の取り込み

**補題。**
\[
\Gamma\vdash_H A:\sigma,\quad\Gamma\vdash_H B:\sigma,\quad
A\equiv_\epsilon B\quad\Longrightarrow\quad A\simeq_\Gamma B.
\tag{H-conversion-completeness}
\]

**証明。** 消去後の合流性から \(A\leadsto^*C\)、\(B\leadsto^*C\) を取る。
各列の長さに関する帰納法で H-step を繰り返す。
型が保存されるため次の段にも H-step を適用でき、
\(\langle A\rangle_\rho=\langle C\rangle_\rho=\langle B\rangle_\rho\) を得る。□

**定理（導出の移送）。**
\[
\Gamma\vdash_+ e:T\Longrightarrow
\epsilon(\Gamma)\vdash_H\epsilon(e):\epsilon(T),\qquad
\Gamma\vDash_+P\Longrightarrow\epsilon(\Gamma)\vDash_H\epsilon(P).
\tag{Coded-embedding}
\]
WF と kind formation についても同様である。

**証明。** 元の全判断の有限導出に関する同時帰納法。
非 conversion 規則は H の定義に含まれる消去後の同じ規則を適用する。
代入を含む結論は Erase-substitution で一致する。
conversion の場合は、二つの formation premise を帰納法で H に移す。
元の raw 同値は Erase-reduction で \(\equiv_\epsilon\) に移るので、
H-conversion-completeness が H-conversion の側条件を与える。□

この帰納法は、簡約によって作った導出の高さが元より小さいことを要求しない。
H-step は先に H の全導出について証明済みであり、有限簡約列に反復するだけである。
\(\mathcal S_+\) 自身の健全性を使って H-step を証明してもいない。

## 相対無矛盾性

**定理。** [型コードモデルの集合論的仮定](coded_model.md)のもとで、
datatype を除いた現行体系について
\[
\neg(\varnothing\vDash_\Box\bot),\qquad
\neg\exists t.\ \varnothing\vdash_\Box t:\bot,
\quad
\bot=\Pi_{(\square^p,*^p,*^p)}X_{*^p}:*^p.X_{*^p}.
\tag{Core-consistency}
\]

**証明。** \(\epsilon(\bot)=\bot\) であり、
\[
\langle\bot\rangle
=\mathbf t(\forall P\in\operatorname{El}(\mathsf p).\ P=1)=0
\]
である。実際 \(0\in\operatorname{El}(\mathsf p)=\mathbb B\)。
Box-free な \(\bot\) の証明があれば、Core-inclusion と Coded-embedding により H に移り、
H-soundness から \(0=1\) を得て矛盾する。
\(t:\bot\) の場合はその消去が \(\bullet:\bot\) なので、\(0\in0\) を得て矛盾する。
Box 付きの導出は [Clear](box_elimination.md) で先に Box-free に移す。□

これは一般の datatype 宣言を含む定理でも、強正規化の定理でもない。
また、従来の非コード化モデルについての TC を解決する必要はなくなったが、
その特定の解釈の TC まで証明したわけではない。

### 依存関係の確認

H-soundness は raw 解釈・集合演算と H の有限導出だけを使う。
H の構造補題は H-soundness を、H-generation はコードの単射性と有限の導入追跡を使う。
H-step はそれらを使い、typing/formation の真部分木について帰納する。
H-conversion-completeness は H-step と raw な合流性を有限列に適用する。
最後の Coded-embedding だけが元の導出について帰納し、その conversion case に
既に証明済みの H-conversion-completeness を使う。
元の体系の健全性や TC から先行する補題へ戻る依存関係はない。
