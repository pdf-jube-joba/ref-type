# 特異余鎖の交換ホモトピー

`On[A, source].forward` は対角写像と Alexander–Whitney 写像の合成である。
`backward` はその後に Koszul 符号付きのテンソル因子交換を施す。
`On.Homotopy.homotopy` は両鎖写像の鎖ホモトピーを与える。

標準単体ごとの模型は \(C_*(\Delta^n)\otimes C_*(\Delta^n)\) である。
両因子への同じ面写像を遷移とし、零次の差が零であることと、正次数の明示的な収縮から模型上の交換ホモトピーを帰納的に構成する。
任意の特異単体への後合成でこれを評価し、自由加群の普遍性によって鎖全体へ延長する。

`Cochains.Pairing[p, q]` は可換環係数の二つの余鎖をテンソル鎖へ評価する。
閉余鎖の評価が全微分を消すことを示し、`HomComplex.Homotopy` によって交換ホモトピーをコホモロジーへ渡す。
`Cochains.GradedCommutativity[p, q].law` は任意のコホモロジー類 \(x,y\) に対して

\[
x\smile y=(-1)^{pq}y\smile x
\]

を与える。
次数 \(p+q\) と \(q+p\) の間の移送は公開される式に明示する。

`Cochains.ExternalCup[p, q]` は積空間の特異鎖について、テンソル余鎖の Alexander–Whitney 写像による引き戻しを、二つの射影で引き戻した余鎖のカップ積と同定する。
`Classes[alpha, beta]` は閉代表の同定とコホモロジー類上の式を与える。
