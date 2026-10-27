# 測度積分の収束

`measure_convergence.On[A, mu]` は `functional_analysis.Measure` の測度と単関数積分に基づく収束定理を公開する。
`monotone` は可測な増加実関数列の各点上限に対する下積分の単調収束を示す。
`FatouFor[f].inequality` は非負可測関数列に対する Fatou の不等式を示す。
左辺は可測な末尾下限の下積分の上限であり、有限の各点下極限があるとき `finiteLiminf` によりその下積分に等しい。
`integral` は可積分実関数の a.e. 同値類上の積分であり、`classIntegral` は代表元による計算を示す。

`Complex` は実部と虚部、`Vector[n]` は有限個の座標をそれぞれ実可積分関数として積分し、a.e. 一致に対する不変性を提供する。
`Examples.zeroIntegral` と `Examples.zeroClassIntegral` は零関数の積分と商上の計算を示す。
