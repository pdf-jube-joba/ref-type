# Euclid 空間の整数階 Sobolev 空間

`Euclidean[n := n].Signed[s := s]` は、重み \((1+|\xi|^2)^{s/2}\) を掛けた Fourier 変換を複素 \(L^2\) の元として表す。
`Order[k := k].Duality[]` は \(H^{-k}\) と \(H^k\) のペアリング、その \(L^2\) 内積との整合性、有界線形汎関数の一意な表現を与える。

`Weak[].ofSchwartz` は実 Schwartz 関数を弱微分で定義した \(W^{k,2}\) に送る。
`Energy[].comparison` は複素 Schwartz 関数について、Fourier ノルムの二乗と、反復微分の \(L^2\) ノルムの二乗を重複度込みで足した値との等式を与える。
`Order[k := k].Density[].sequenceExists` は、この Schwartz 関数の像で任意の \(H^k\) の元を近似する。

`Transport` は開集合間の微分同相による引き戻しにコンパクト台の滑らかな係数を掛け、零延長した作用素を正負の次数に与える。
`MultiplicationBy` は恒等写像に対する場合で、実数値の滑らかなコンパクト台関数による乗算を与える。

`EmbeddingTheorem[r := r, p := p, range := range].theorem` は \(2p>n\) のとき、\(H^{r+p}\) の元の逆 Fourier 積分が \(C^r\) 級になることを示す。
`Regularity[].smooth` は全ての非負整数次数に属する元に対し、各次数で共通の滑らかな逆 Fourier 積分を与える。
