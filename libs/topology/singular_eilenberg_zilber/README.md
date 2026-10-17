# Eilenberg–Zilber 比較

積空間の特異鎖と、二つの特異鎖複体のテンソル積の全複体を比較する。
`singular_products` の Alexander–Whitney 写像と shuffle 写像を、両側の鎖ホモトピーとともに公開する。

`On[A, B, left, right]` の `forward` は Alexander–Whitney 写像、`backward` は shuffle 写像である。
`productComposite` は積空間側、`tensorComposite` はテンソル積側の合成である。
`Equivalence.equivalence` は非負次数の鎖ホモトピー同値を返し、`Equivalence.Signed.equivalence` は負次数を零で延長した整数次数の同値を返す。

積空間側では、標準単体の積の対角特異単体に対する合成の差を埋める。
テンソル積側では、標準単体二つの特異鎖のテンソル積をモデルとする。
面の交代和によるモデル間の写像と鎖境界が可換することを示し、各モデルの収縮を用いて次数ごとに埋める。
次数零の差が零であるため、正次数から始める再帰でホモトピーを構成する。

`TensorEvaluation` はモデル上の鎖を任意の特異単体の組へ評価する。
`TensorGenerators` は全複体の各次数を生成する純テンソルを与え、`TensorHomotopy` はモデル上の埋め合わせをこの生成元から延長する。
両側のホモトピーは、生成元上の境界公式と線形性から鎖ホモトピーの等式を満たす。
