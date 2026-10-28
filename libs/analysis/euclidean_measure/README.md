# Euclid 空間の測度

`euclidean_measure.Euclidean[n]` は閉直方体の可算被覆に基づく外測度候補を構成する。
直方体の各辺の長さの積を体積とし、空の直方体も許す。
被覆の費用は拡張非負実数の下切断として表した体積の級数であり、`outer` は被覆費用の下限を丸めた下切断である。

`outerNonnegative`、`monotone`、`outerEmpty`、`boundedByCover`、`greatestLowerBound` は下限の基本性質を示す。
`boxUpper` は直方体の外測度が体積以下であることを示す。
`translationInvariant` は平行移動不変性を示し、`scaledVolume` は非負の座標ごとの拡大に対する直方体の体積の変換を示す。
`Positive[k].singletonNull` は正の次元における一点集合の外測度が零であることを示す。

`Caratheodory` は外測度による分割条件であり、空集合と補集合について成立し、互いに素な集合について有限加法性を与える。
`Examples` はこれらの利用例を含む。
