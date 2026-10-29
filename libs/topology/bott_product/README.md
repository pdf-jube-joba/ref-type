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
`Slice.Relative.Retraction.injective` は基点切片への再射影と完全列により、相対群からの忘却写像が単射であることを示す。
`Slice.Relative.Retraction.Comparison` は相対類と \(K^0(X)\) の係数を対応させ、加法を保つ両方向の逆写像を与える。

`Product.Injective.injective` と `Product.Surjective.exists` は標準積が加法群として全単射であることを示す。
`Product.Inverse.first` は基点制限、`coefficient` は復元式を満たす唯一の係数を返す。
実束から境界ループを作り K07 の逆クラスを取る `Product.Bundle.Decomposition` と `Product.Surjective` の構成は、この係数を計算する。
`Inverse.ofRepresentation` は構成に用いた選択によらず計算結果が一致することを示す。

`Bott.Powers.squareLoop` は境界関数 \(z^2\) の clutching 線束の被約類が \(2u\) であることを示す。
`Bott.TensorLine` はテンソル平方の両半球上の枠を比較し、\(z^2\) の clutching 束への大域同型を構成する。
`Bott.Square.zero` は \(u^2=0\) を示し、`Product.Multiplication.formula` は標準積の係数による乗法公式を示す。
`Bott.Sign.negative` は円周係数を複素共役にした clutching 類が \(-u\) になることを示す。
`Bott.ProjectiveLine.SphereLine.Comparison.universalIsomorphism` は射影直線の普遍線束の球面上への引き戻しと共役 clutching 線束を同一視する。
`Comparison.Class.sign` は普遍線束の被約類 \([H]-1\) が `Bott.generator` の負であることを示す。
`Product.Coefficients` は係数対の加法と乗法、標準写像とその逆写像、および加法・乗法との両立を与える。
`Product.Coefficients.Ring` は係数対を交換環にし、標準積を環準同型として与える。
`Product.Polynomial` は関係式 \(u^2=0\) を持つ多項式商と標準積への環準同型を構成し、`Polynomial.Normal` は各式の正規形と具体的な両側逆写像を証明する。
普遍線束の被約類を生成元に選ぶ場合、`Product.Hopf` は符号を反映した標準積と係数逆写像を、`Product.Hopf.Polynomial` は対応する多項式商の環同型を与える。
`Product.Naturality.Hopf` はこの標準積と逆写像の自然性を示し、`Slice.Relative.Retraction.Comparison.Hopf` は相対群との係数対応を同じ符号で与える。
