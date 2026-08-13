# Core calculus に入れるべき

## 実装済み

### 証明と証明項の抽象化
$P: *^p$ に対して $t: P$ の項を区別する必要はなく、存在することだけ取り出せればよいはず。
- $\Gamma \vDash P$ を 「$\Gamma$ の下で $P$ が証明可能」を表すように導入する。
- $\Gamma \vDash P$ ならその証明項を具体的に扱わなくてもいいように、 $\Gamma \vdash \Proof P: P$ という項を導入できるようにする。

### refinement type と power type と predicate の導入
"集合" $A$ に対して $\{x: A \mid P\}$ や $\Power A$ が書けるとうれしい。
さらに、 $\{x: A \mid P\}$ から述語が取り出せた方が扱いやすい。
このため、 $\Pred(A, B, t)$ という項を入れて、 $\Pred(A, \{x: B \mid P\}, t) \to_\beta (\lambda x: B. P) @ t$ のように関係を導入する。
こうすれば、一般の $A$ と $B$ に対して、 $t: A$ が $t: B$ になる条件を記述できる。
ただし、 term のレベルと type のレベルを合わせたいので次のような感じにしている。
| 説明 | term level | type level |
| --- | --- | --- |
| 普通の項 | $t$ | $A$ |
| Power set の元 | $\{x: A \mid P\}, B$ | $\Power A$ |
| subset 関係 | $t$ | $\Ty (A, \{x: A \mid P\}), \Ty (A, B)$ |

### definite description について
商集合を扱うことができるようになったので、これをさらに便利にするために、 quotient のようなことができるとうれしい。
一応すでに商集合自体は記述ができるが、写像を記述することが難しい。
これを動機として、 $\Take x: T. t$ を $t: M$ が $x$ の元の取り方に**よらず**に定まるときに、 $M$ の元として扱う。
これの正当性を記述するために $=$ や"元の存在"が必要になる。

## 未実装

### non structural recursion を書きたい
Coq では
