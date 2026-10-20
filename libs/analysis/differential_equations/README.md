# 微分方程式

`Euclidean[n].BoundedLipschitzField` は、最大値ノルムについて有界で Lipschitz な自律ベクトル場を表す。
`On[field, initial]` は、その定数から正の時間幅を選び、初期値を中心とする半径一の連続曲線の閉球上に Picard の積分作用素を構成する。

連続曲線の空間の完備性、積分のノルム評価、二つの入力に対する積分の差の評価から、作用素が閉球を保つことと縮小率が高々 \(1/2\) であることを証明する。
Banach の不動点定理で得た曲線を `curve` として公開する。

`On.Solution.value` は実数上の関数で、構成した時間区間上で曲線と一致する。
`initialValue` は初期値、`continuous` は閉時間区間上の連続性、`derivative` は区間内部で各座標が \(y'=F(y)\) を満たすことを示す。
`integralEquationUnique` は、この閉球内で Picard の積分方程式を満たす曲線の一意性である。
