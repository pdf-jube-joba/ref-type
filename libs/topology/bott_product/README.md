# Bott の基本積

`Bott.ProjectiveLine.Homeomorphism.homeomorphism` は、複素2次元空間の階数1直交射影の空間と \(S^2\) の具体的な同相を与える。
順写像は射影行列の成分から実3座標を作り、逆写像は球面上の点から跡1のエルミート冪等行列を作る。
`ProjectiveLine.SphereLine` は普遍線束をこの同相に沿って球面へ引き戻す。

`Bott.generator` は単位円の座標による clutching 線束と自明線束の差である。
`Rank.zero` と `Restriction.vanishes` は、この類のランクと一点への制限が零であることを示す。
`Product.forward` は2つの射影に沿う引き戻しと積によって \(a+b u\) を与え、`Product.At.restrictForward` と `Product.Naturality.equation` は基点への制限と自然性を示す。

`Product.Loops.With.forwardFormula` は K07 の行列ループの逆クラスをこの積に結び付ける。
`Product.Bundle.Preparation.With` は基点制限の補束による安定化と両半球上の自明化を構成する。
`Transition.With` は境界上の自明化から連続可逆行列ループを構成する。
`Product.Surjective.exists` は任意の \(K^0(X\times S^2)\) の類について、標準積による表示の存在を示す。

`Product.At.Kernel` は基点制限の核が生成元を掛けた類の像であることを示す。
`Product.At.Slice` は基点の切片と \(X\) の具体的な同相を構成し、`Slice.Relative.imageRepresentation` は K03 の相対群から忘却された類がこの像に入ることを示す。

`Product.Injective.injective` と `Product.Surjective.exists` は標準積が加法群として全単射であることを示す。
`Product.Inverse.first` は基点制限、`coefficient` は復元式を満たす唯一の係数を返す。
実束から境界ループを作り K07 の逆クラスを取る `Product.Bundle.Decomposition` と `Product.Surjective` の構成は、この係数を計算する。
`Inverse.ofRepresentation` は構成に用いた選択によらず計算結果が一致することを示す。
