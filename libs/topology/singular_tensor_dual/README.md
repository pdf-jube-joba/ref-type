# 有限自由鎖のテンソル双対

`Over[R, ring]` は可換環上で定義する。
`Finite[V, rank].Frame` は有限個の元と線形汎関数による恒等写像の分解であり、有限自由基底だけでなく有限射影加群の双対フレームも含む。
標準座標加群のフレームは `Finite.Coordinates.frame`、有限座標への基底同型からのフレームは `Finite.FromIsomorphism[e].frame` で得られる。

`On[P, Q, ranks, frames]` は非負次数の鎖複体 \(P,Q\) と、各 \(P_n\) の有限双対フレームを受け取る。
\(Q_n\) の有限性や複体全体の有界性は必要ない。
各次数の対角線 \(p+q=n\) は有限である。

`source` は \(\operatorname{Tot}(\operatorname{Hom}(P,R)\otimes_R\operatorname{Hom}(Q,R))\)、`target` は \(\operatorname{Hom}(\operatorname{Tot}(P\otimes_R Q),R)\) である。
`forward` と `backward` は互いに逆の余鎖写像であり、`equivalence` は零ホモトピーを備えた余鎖ホモトピー同値である。
`Degree[n].isomorphism` は各次数の加群同型を与える。

`Evaluation[n, i].law` は \(i=(p,q)\) の成分について

\[
(\varphi\otimes\psi)(x\otimes y)=\varphi(x)\psi(y)
\]

を示す。
微分の符号はテンソル複体の水平項と \((-1)^p\) を伴う垂直項に従う。
局所的な逆写像は双対フレーム \((e_i,e^i)\) を用いて

\[
h\longmapsto\sum_i e^i\otimes\bigl(y\longmapsto h(e_i\otimes y)\bigr)
\]

と構成する。
