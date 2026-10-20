# ユークリッド空間へのはめ込みの法束

`Dimension[n := n, k := k].On[M := M].Of[i := i]` は滑らかなはめ込み \(i:M\to\mathbb R^{n+k}\) の法束を構成する。
底点は像の点に置き換えず \(M\) に保つため、自己交差を持つはめ込みにも適用できる。
`Point` は底点と法ベクトルの依存対であり、`At[x].subspace` は
\[
\{w\in\mathbb R^{n+k}\mid\forall v\in T_xM,\ \langle w,di_xv\rangle=0\}
\]
という部分空間である。

| API | 内容 |
| --- | --- |
| `Fiber` / `fiberSpace` / `fiberDimension` | ファイバー、ベクトル空間、\(k\) 個の有限基底 |
| `At.Quotient.isomorphism` / `onClass` | \(\mathbb R^{n+k}/\operatorname{im}(di_x)\) と法空間の標準的な線形同型 |
| `Local` / `LocalFrame.At.isomorphism` | 近傍上の滑らかな正規直交枠と相互逆の局所自明化 |
| `covers` / `changes` / `manifold` | 局所枠による被覆、滑らかな遷移、\(n+k\) 次元の全空間 |
| `SubspaceTopology.explicitHomeomorphism` | \(M\times\mathbb R^{n+k}\) の直交条件を満たす部分空間との同相 |
| `Projection` / `Zero` / `Addition` / `Scaling` | 射影、零切断、ファイバー演算とその滑らかさ |
| `Vector.map` / `FromAmbient.From.Of` | 法ベクトルの周囲空間への表示、滑らかな直交ベクトル族からの写像構成 |
| `Splitting.diffeomorphism` | \(TM\oplus\nu_i\to M\times\mathbb R^{n+k}\) の微分同相 |
| `BaseChange.Between.Of` | 底空間の微分同相を覆う、周囲ベクトルを保つ法束の微分同相 |
| `Stabilization.On.Of` | 標準包含による \(\nu_{i^+}\cong\nu_i\oplus\varepsilon^1\) と直和分解との整合性 |

局所枠の存在は `InChart` と `Cover` で、微分の単射性から証明する。
まず滑らかな Gram–Schmidt 分解で接方向を正規直交化し、その直交補空間への滑らかな射影を得る。
`calculus.ProjectionFrames` は射影の非零列を選び、ノルムが正である開近傍へ縮め、正規化と射影の階数を一つ減らす操作を帰納的に行う。
これは基準点の法基底を近傍へ射影し、Gram–Schmidt を行う操作を、射影の列とトレースを使って実装したものである。
分母の正値性、平方根と逆数の滑らかさ、階数が余次元に等しいことをこの構成に含める。

直和分解は \((x,v,w)\mapsto(x,di_xv+w)\) である。
逆写像は直交射影と、接方向の Gram–Schmidt 分解から得る微分の像上の逆写像を使う。
この分解から滑らかな法方向へのレトラクションを作り、局所自明化の位相が周囲の積の部分空間位相に等しいことも証明する。
安定化は周囲ベクトルの最後に実数座標を追加し、有限添字の次元の等式は等長線形同型によって移送する。

具体的な座標包含と放物線は [tangent_normal](../examples/tangent_normal/README.md) にある。
一般のベクトル束、境界付き多様体、埋め込みの存在定理、管状近傍定理はそれぞれ後続の対象とする。
