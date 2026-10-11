# 射影分解と複体の構成

非負鎖複体、射影分解、比較定理、Hom・テンソル複体、二重複体を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`resolutions.NonnegativeChain.Over.ZeroExtension` は `DegreeZeroHomology`・`PositiveHomology`・`NegativeHomology` で元のホモロジーとの同型と負次数の消滅を公開する。
`resolutions.Resolution.Over` は非負次数の射影分解と、比較写像・比較写像の鎖ホモトピーによる一意性を扱う。
`resolutions.Resolution.Over.ShortExact.Sequence` は増大写像と整合する分解の短完全列を束ねる。
`Morphism.With.existence` は係数の可換図式を鎖複体の可換図式へ持ち上げる。
`resolutions.NonnegativeChain.Over.ShortExact.Morphism.Straighten` は比較写像をホモトピーで補正し、増大写像を保った可換図式を構成する。
`resolutions.ResolutionTensor.Over.Of.With` は射影加群と指定した射影分解のテンソルから分解を構成し、増大写像の全射性、完全性と各項の射影性を証明する。
`resolutions.TensorComplex.Over.Square.With.naturality` はテンソル積が鎖写像の可換図式を保つことを示す。

実数上の具体化と、次数ごとに台集合が変わる利用例は [Cohomology.ref](../../tests/projects/manifolds-de-rham/src/Cohomology.ref) にある。

検査方法と関連パッケージは [ライブラリ一覧](../README.md) を参照。
