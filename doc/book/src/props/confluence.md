拡張した体系として、部分型・べき・述語・存在・take を入れてた。
これの confluence を示す。
Tait-Martin-Lof の parallel reduction と Takahashi の $M^*$ を使えばできそう。
term はだいたい cong にやってるが、次のものだけ追加されている。
- $\Pred (A, \{x: t \mid P \}) \rightarrow^\beta \lambda x:t. P$

これに合わせて、 parallel reduction と $M^*$ は次のものを入れておけばいい。
- $\Pred (A, \{x: t \mid P\}) \Rightarrow \lambda x: t'. P'$ if $t \Rightarrow t', P \Rightarrow P', A \Rightarrow A'$
- $\Pred (A, B) \Rightarrow \Pred(A', B')$ if $A \Rightarrow A', B \Rightarrow B'$
- $(\Pred (A, \{x: t \mid P\}))^* = \lambda x: t^*. P^*$ 

としておく。
# ちゃんと全部書いておく
## parallel reduction
base case
- $s \Rightarrow s$
- $x^s \Rightarrow x^s$
cong case
- $(x^s: A) \to B \Rightarrow (x^s: A') \to B'$ if $A \Rightarrow A', B \Rightarrow B'$
- $\lambda x^s: A. B \Rightarrow \lambda x^s:A'. B'$ if $A \Rightarrow A', B \Rightarrow B'$
- $A B \Rightarrow A' B'$ if $A \Rightarrow A', B \Rightarrow B'$
- $(\lambda x^s: A. M) B \Rightarrow M'[x := B']$ if $A \Rightarrow A', B \Rightarrow B', B \Rightarrow M'$
- $\{x: A \mid P\} \Rightarrow \{x: A' \mid P'\}$ if $A \Rightarrow A', P \Rightarrow P'$
- $\Power A \Rightarrow \Power A'$ if $A \Rightarrow A'$
- $\Pred(A, B) \Rightarrow \Pred(A', B')$ if $A \Rightarrow A', B \Rightarrow B'$
- $a =_A b \Rightarrow a' =_{A'} b'$ if $A \Rightarrow A', a \Rightarrow a', b \Rightarrow b'$
- $\Take x: A. B \Rightarrow \Take x: A'. B'$ if $A \Rightarrow A', B \Rightarrow B'$ 
- $\exists A \Rightarrow \exists A'$ if $A \Rightarrow A'$
redux case
- $\Pred(A, \{x: B \mid P\}) \Rightarrow \lambda x: B'. P'$ if $A \Rightarrow A', B \Rightarrow B', P \Rightarrow P'$
- $\Proof P \Rightarrow \Proof P'$ if $P \Rightarrow P'$

Remark: beta reduction はここから次のように制限したものになる。
- $s \Rightarrow s$ と $x^s \rightarrow x^s$ を抜く
- sub term はそれぞれ一つだけ reduction を進める
  - 例： $(x^s: A) \to B \to_beta (x^s: A') \to B$ みたいに、 $A$ が進んだときは $B$ を進めない。
- $(\lambda x^s: A. M) B \to_beta B[x := A]$ のような redux は subterm を進めない。 $\Pred(A, \{x: B \mid P\}) \to_beta \lambda x: B. P$ もそう。

#### $M \Rightarrow M$
base case と congruent なやつを使えば、 $M$ の構造についての帰納法でよい。

#### $M \to_\beta N$ なら $M \Rightarrow N$
$\to_beta$ の構成に関する帰納法でよい。
このさいに $M \Rightarrow M$ が必要になる。
$\to_\beta$ も congruent に定義しているところでは、そのまま次のような議論が使える。
- $M N \to_beta M' N$ で $M \to_beta M'$ のとき、帰納法の仮定から $M \Rightarrow M'$ が得られて、 $N \Rightarrow N$ と合わせて par.red ができる。
そうじゃなくて、 redux っぽいところはこれも対応する par.red を考えればいい。
- $(\lambda x^s: A. M) B \to_\beta M [x := B]$ のとき、 $M \Rightarrow M, B \Rightarrow B, A \Rightarrow A$ から、これと par.red ができる。
- $\Pred(A, \{x: B \mid P\}) \to_\beta \lambda x^{*^s}:B. P $ のときは、これも上と同様。

#### $M \Rightarrow N$ なら $M \to_\beta^* N$
$M \Rightarrow N$ の構成に関する帰納法でよい。
- base case に対しては、 $\to_beta^*$ は reflective + transitive な閉包なので、 reflective の方からわかる。
- cong case に対しては、帰納法の仮定から楽にできる。
  - 例： $M N \Rightarrow M' N'$ if $M \Rightarrow M', N \Rightarrow N'$ に対しては、帰納法の仮定から $M \to_\beta^* M', N \to_\beta N'$ が得られていて、 $\to_\beta$ の cong の方を適用すればいい。
- redux case に対しては、これも redux + 帰納法の仮定からわかる。
  - 例：$(\lambda x^s: A. M) B \Rightarrow M'[x := B']$ if $A \Rightarrow A', B \Rightarrow B', M \Rightarrow M'$ のとき：
  帰納法の仮定から、 $A \to_\beta^* A', B \to_\beta^* B', M \to_\beta M'$ が得られている。よって、 $(\lambda x^s: A. M) B \to_\beta^* \lambda (x^s: A'. M') B' \to_\beta M'[x := B']$ になる。

他は全部同じようにできる。

#### 代入順序の交換について
$M[x := L][y := N[x := L]] = M[y := N][x := L]$ が成り立つ。
（ただし、束縛変数に関する条件があるので注意）

#### $M \Rightarrow M', N \Rightarrow N'$ なら $M[x: = N] \Rightarrow M'[x: = N']$
binding を行うような項（ $(x^s: A) \to B$, $\lambda x: A. B$, $\{x: A \mid P\}$, $\Take x: A. B$ ）は、α同値で代入する変数とかぶらないようにしておく。
（もっと強く、 $\text{BV}(M)$ が $\text{FV}(M)$ や $\text{FV}(N)$ とかぶらないようにしておいてもいい。）

$M \Rightarrow M'$ の構成に関する帰納法でよい。
base case
- $s \Rightarrow s$ に対しては代入で何も変わらないから。
- $x^s \Rightarrow x^s$ に対しては、 $N \Rightarrow N'$ になるか $x^s \Rightarrow x^s$ になるか。
cong case:binding に関する仮定を考えると（考えなくても $M \Rightarrow M$ があるのであまり変わらないけれど）代入が cong に進むだけなので、帰納法の仮定と合わせればよい。
- $(\lambda y^s: A. B)[x := N] \equiv \lambda y^s: A[x := N]. B[x := N] \Rightarrow \lambda y^s: A'[x := N']. B'[x := N'] \equiv (\lambda y^s: A'. B')[x := N']$
redux case: この場合、代入の順序の入れ替えに関する補題を用いる必要がある。
- $((\lambda y^s: A. M) B) \Rightarrow M'[y := B']$ if $A \Rightarrow A', M \Rightarrow M', B \Rightarrow B'$ に対して、
  帰納法の仮定から $M[x := N] \Rightarrow M'[x := N'], B[x := N] \Rightarrow B'[x := N']$ が得られている。
  示したいのは次のもの。
  $$ ((\lambda y^s: A. M) B)[x := N] \Rightarrow (M'[y^s := B'])[x := N'] $$
  ここで、 $((\lambda y^s: A. M) B)[x := N] \equiv (\lambda y^s: A[x := N]. M[x := N]) B[x := N] \Rightarrow (M'[x := N'])[y := B'[x := N']] \equiv M'[y := B'][x := N']$ である。（ここで束縛の仮定を用いることになる。）
- $\Pred(A, \{y: B \mid P\}) \Rightarrow \lambda y^{*^s}:B'. P'$ のとき。帰納法の仮定から $B[x := N] \Rightarrow B'[x := N']$ と $P[x := N] \Rightarrow P'[x := N']$ が得られている。なので、 $\Pred()[x := N] = \Pred(A, \{y \mid B[] \mid P[]\}) \Rightarrow \lambda y: B'[]. P'[]$ からわかる。

## $M^*$ を作る
base case
- $s^* = s$
- $x^* = x$
redux case
- $((\lambda x: A. M) B)^* = M^*[x := B^*]$
- $\Pred(A, \{x: B \mid P\})^* = \lambda x: B^*. P^*$
cong case
- $(M N)^* = M^* N^*$ if $M \not \equiv \lambda x: A. B$
- $\Pred(A, B)^* = \Pred(A^*, B^*)$ if $B \not \equiv \{x: C \mid P\}$
- $((x: A) \to B)^* = (x: A^*) \to B^*$
- ...

#### $M \Rightarrow N$ なら $N \Rightarrow M^*$
$M$ の構造に関する帰納法を用いる。
（$M$ の構造を見ることで $M \Rightarrow N$ が何でえられているか制限できることに注意）
- $M \equiv x, s$ の場合、 $M \Rightarrow N$ は base case でしか与えられない。なので、 $N \equiv M$ であるから、 $M^* \equiv M$ と合わせて成り立つ。
- $M$ が redux の形にならない場合、 $M \Rightarrow N$ は cong case でしか与えられない。この場合には帰納法の仮定を用いることで証明できる。
  - 例： $M \equiv (x: A) \to B$ のときには $N \equiv (x: A' \to B')$ で $A \Rightarrow A', B \Rightarrow B'$ であることがわかる。
    このとき、帰納法の仮定から、 $A \Rightarrow A' \Rightarrow A^*, B \Rightarrow B' \Rightarrow B^*$ が得られているので、 $(x: A') \to B' \Rightarrow (x: A^*) \to B^*$ である。
- $M$ が redux の形になっている場合、 $M \Rightarrow N$ の構成に使ったルールは複数ありうるので、場合分けする。
  - $M \equiv (\lambda x: A. M) B$ のとき。
    - $N \equiv (\lambda x: A'. M') B'$ で cong なときには、帰納法の仮定から $M \Rightarrow M' \Rightarrow M^*$ などが成り立っている。
      この場合には、 $(\lambda x: A'. M') B' \Rightarrow M^*[x := B^*]$ が使える。
    - $N \equiv M'[x := B']$ で $M \Rightarrow M', B \Rightarrow B'$ のときには帰納法の仮定と補題を用いて、 $M'[x := B'] \Rightarrow M^*[x := B^*]$ がわかる。
  - $M \equiv \Pred(A, \{x: B \mid P\})$ のとき。
    - $N \equiv \lambda x: B'. P'$ のときには帰納法の仮定から $B' \Rightarrow B^*$ と $P' \Rightarrow P^*$ が得られているので、 $\lambda x: B'. P' \Rightarrow \lambda x: B^*. P^*$ である。
    - $N \equiv \Pred(A', \{x: B' \mid P'\})$ のときには帰納法の仮定から $B' \Rightarrow B^*$ などが得られているので $\Pred(A', \{x: B' \mid P'\}) \Rightarrow \lambda x: B^*. P^*$ である。

#### confluence
$M \Rightarrow M_1, M_2$ でも $M_1, M_2 \Rightarrow M^*$ がわかるので、 $\Rightarrow$ は合流性があるから、これに挟まれている $\to_\beta$ も合流性がある。
