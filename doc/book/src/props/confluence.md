拡張した体系として、部分型・べき・述語・存在・take を入れてた。
これの confluence を示す。
Tait-Martin-Lof の parallel reduction と Takahashi の $M^*$ を使えばできそう。
term はだいたい cong にやってるが、
- $\Pred (A, \{x: t \mid P \}) \rightarrow^\beta \lambda x:t. P$

だけ追加されている。
- $\Pred (A, \{x: t \mid P\}) \Rightarrow \lambda x: t'. P'$ if $t \Rightarrow t', P \Rightarrow P', A \Rightarrow A'$
- $(\Pred (A, \{x: t \mid P\}))^* = \lambda x: t^*. P^*$ 

で多分できるんじゃない？
