# 体系の検討事項

Set case と induction は declaration から生成される通常の規則を持つ。

## 課題
- datatype declaration environment の well-formedness と positivity 判定
- Set の鏡像に対する case と induction の raw syntax、typing、reduction の生成規則
- inductive type や record を定義する際に気を付けるのは、dependent sum type と W-type にしたときの大きさ
    - 基本的には \(\mathcal{R}\) と同じものを使ってよい。
    - impredicative にならないように、\((*^s, *^p, *^s) \in \mathcal{R}\) にすること。
        - これが必要になるのはおかしい気がする（subtype で対応するべきだから。）。
- judgement を stratified（\(\Gamma \vdash^s t: T\)）にしなくてもいいのでは...
- \(\Ty\) を2引数にしない場合
    - \(\Ty(A, B)\) の代わりに \(t: \Ty B\) と \(B: \Power A\) を premise に入れる。
- take elim prop の set-theoretic な意味は、普通に \(\bullet \in \lbrack T \rbrack\) への map になっているということ？
    - take elim は \(X: *^p\) なら cut elimination に見える。
- reduction の仮定にあらわれる合同性について：
    - Pred: \(\Pred (A, \{x: B \mid P\}, t) \Rightarrow_s (\lambda x: B. P) @ t\) としたが、同値関係としての \(\beta\) を定めるときには、\(\Pred (A, \{x: B \mid P\}, t) \cong (\lambda x: B. P) @ t\) if \(A \cong B\) のようにしてもいいかも。
