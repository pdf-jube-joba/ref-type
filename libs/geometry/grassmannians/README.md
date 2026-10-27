# 有限 Grassmannian

有限次元の実・複素 Grassmannian とその普遍束を扱う。
公開入口 `Real[n, k].Model[].Carrier` と `Complex[n, k].Model[].Carrier` は、それぞれ標準 \(n\) 次元空間上の直交射影のうち、像が \(k\) 個の基底を持つものの型である。
射影と階数は `hermitian_frames` の `Projection` と `OnProjection.Rank.HasRank` を再利用する。
`Examples` は任意の周囲次元で恒等射影と基底を構成し、特に零次元の Grassmannian と階数1の実・複素射影空間に具体的な点を与える。

射影の行列成分から誘導位相を構成し、連続射影族の像として普遍束とその直交補束を構成する。
各点の近傍に連続な正規直交フレームが存在する。
`Real.Model` と `Complex.Model` は線形写像をデータとし、射影と階数の条件を課した表現である。
この表現について行列成分の単射性、Hausdorff 性、正規直交フレーム空間からの連続全射によるコンパクト性を証明し、普遍束・直交補束・連続な直和写像を構成した。
`ProjectiveReal` と `ProjectiveComplex` はこのモデルを階数1に特殊化し、標準線束と直交補束を公開する。
連続な一定階数の射影族から Grassmannian への連続写像を `Family.map` として構成する。
任意の連続写像による普遍束の引き戻しと、合成した射影族の像束との同型を `Pullback.isomorphism` として公開する。
直和では、ブロック射影の階数加法と写像の連続性を証明する。
`Graph` は基準点の近傍で射影像を基準部分空間からその直交補へのグラフとして表し、像の復元を証明する。
`Model.Graph.Reconstruction.homeomorphismExists` は局所グラフ座標を順写像とする同相写像の存在を証明し、`Model.Charts.exists` は各点でこの座標の存在を与える。
零射影・恒等射影との直和から、周囲次元と階数を安定化する連続写像を構成する。
直交補写像と、引き戻した普遍束から元の直交補束への同型を構成する。
直和写像に沿う普遍束の引き戻しと、両因子から引き戻した普遍束の直和との同型を構成する。
安定化についても、普遍束の引き戻しと各因子から引き戻した束の直和との同型を構成する。
既存の `bundle_complements.Projection` は連続な射影族から像束を構成し、`Projection.Pullback` は引き戻しを比較する。
`hermitian_frames` は射影の直交補とブロック和を提供する。
元の `Real.Grassmannian`・`Complex.Grassmannian` は射影構造体に基づく補助表現で、Model との両方向の連続写像と Model 側の往復等式を提供する。

`Stabilization.ambientBundleIsomorphism` と `dimensionBundleIsomorphism` の右辺は、各因子の普遍束を直和の基底から安定化の基底へ順に引き戻した束の直和である。
同型の基底写像が公開する安定化写像と一致することは `ambientMapFormula` と `dimensionMapFormula` が示す。

検査と再開方法は `work/b05-resume.md` に記載する。

対象と依存先の検査結果は [検査記録](../../../benchmarks/records/grassmannians/README.md) にある。
