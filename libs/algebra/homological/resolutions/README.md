# 射影分解と複体の構成

射影分解、比較定理、Hom・テンソル複体と二重複体による分解比較を扱う。
非負鎖複体と二重複体の基盤は [double_complexes](../double_complexes/README.md) にある。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`resolutions.Resolution.Over` は非負次数の射影分解と、比較写像・比較写像の鎖ホモトピーによる一意性を扱う。
`resolutions.Resolution.Over.ShortExact.Sequence` は増大写像と整合する分解の短完全列を束ねる。
`Morphism.With.existence` は係数の可換図式を鎖複体の可換図式へ持ち上げる。
`resolutions.ResolutionTensor.Over.Of.With` は射影加群と指定した射影分解のテンソルから分解を構成し、増大写像の全射性、完全性と各項の射影性を証明する。
`resolutions.TensorComplex.Over.Square.With.naturality` はテンソル積が鎖写像の可換図式を保つことを示す。

`ResolutionTensor.Over.Double` は二つの射影分解のテンソル total と各項の射影性を構成する。
`With.standardLeft`・`standardRight` は各増大写像から片側だけを分解したテンソル複体への比較鎖写像を返す。
`With.LeftQuasi`・`RightQuasi` は行・列の完全性から比較写像のホモロジー同型を証明し、`At.isomorphism` と実際の誘導写像との一致を公開する。
`Naturality.With.Left.square`・`Right.square` は、増大写像と整合する二つの分解写像と係数写像について比較鎖写像の可換図式を与える。
`With.Swap.rightSquare`・`leftSquare` は Koszul 符号付きの因子交換と左右の比較写像との整合性を証明する。
`With.LeftInjection`・`RightInjection` は直和の各成分上の比較写像の公式を与える。

実数上の具体化と、次数ごとに台集合が変わる利用例は [Cohomology.ref](../../../../libs/geometry/coordinate_calculus/src/Cohomology.ref) にある。

検査方法と関連パッケージは [ライブラリ一覧](../../../README.md) を参照。
