# Euclid 空間の測度

`euclidean_measure.Euclidean[n]` は閉直方体の可算被覆に基づく外測度を構成する。
直方体の各辺の長さの積を体積とし、空の直方体も許す。
被覆の費用は拡張非負実数の下切断として表した体積の級数であり、`outer` は被覆費用の下限を丸めた下切断である。

`outerNonnegative`、`monotone`、`outerEmpty`、`boundedByCover`、`greatestLowerBound` は下限の基本性質を示す。
`boxUpper` は直方体の外測度が体積以下であることを示す。
`Countable.subadditive` は可算劣加法性、`subadditivePair` は有限劣加法性、`nullCaratheodory` は外測度が零の集合の可測性を示す。
`translationInvariant` は平行移動不変性を示し、`scaledVolume` は非負の座標ごとの拡大に対する直方体の体積の変換を示す。
`Positive[k].singletonNull` は正の次元における一点集合の外測度が零であることを示し、`countableNull` は可算点集合に拡張する。
`Zero.singletonVolume` は零次元の一点集合の外測度が 1 であることを示す。

`Caratheodory` は外測度による分割条件であり、空集合、補集合、有限和集合、有限共通部分について成立し、互いに素な集合について有限加法性を与える。
`weave` は二つの被覆列を交互に並べ、その費用が元の費用の和になる。
`CaratheodorySets.sigma` は Carathéodory 可測集合の σ-代数、`MeasureConstruction.measure` は外測度を制限した完備測度である。
`MeasureConstruction` は平行移動不変性と零集合の可算和を提供する。
`Scaling` は正の座標ごとの拡大について、可測性と測度の変換を示す。
`Borel` は Euclid 位相の開集合を含む最小の σ-代数を構成する。
`EuclideanBorel` はすべての次元で開集合と Borel 集合の可測性を示す。
`Examples` はこれらの利用例を含む。

`CoverExpansion.outerRegular` は、任意集合の外測度が、それを含む開集合の外測度の下限に一致することを示す。
`InnerRegular.innerRegular` は、可測集合の測度がその内部に含まれるコンパクト集合の測度の上限に一致することを示す。
これらの等式は無限測度も含め、下切断によって記述する。
`BoxCompact.compact` は閉直方体のコンパクト性、`Exhaustion` は全空間を尽くす増大する箱列を示す。
`GdeltaHull.finiteHull` は有限外測度の集合を同じ外測度の Gδ 集合で包む。

`BoxVolume.boxVolume` は、閉直方体の外測度が辺の長さの積と一致することを示す。
`Hyperplane.null` は座標超平面が零集合であることを示す。
`GeneralDiagonal.formula` は符号と零係数を含む任意の対角拡大について、可測性と測度の変換則を示す。
`RealLine` は実数直線への測度の移送と区間の長さを提供する。
`RealLine.RiemannMap` は任意の Riemann 可積分関数の区間制限を測度可積分関数として構成し、その積分値の一致を示す。
`RealLine.CompletionAgreement.agreement` は既存の L1 完備化の任意の元について、同じ積分値を持つ測度可積分な代表の存在を示す。
この代表は完備化の Cauchy 列から、差の L1 ノルムが総和可能な部分列を選び、その概至る所での極限を取って構成する。
