# 有限 Grassmannian

B05 の作業中パッケージである。
`Real[n, k].Grassmannian` と `Complex[n, k].Grassmannian` は、それぞれ実・複素の標準 \(n\) 次元空間上の直交射影のうち、像が \(k\) 個の基底を持つものの型である。
射影と階数は `hermitian_frames` の `Projection` と `OnProjection.Rank.HasRank` を再利用する。
`Examples` はゼロ次元の恒等射影と基底を構成し、実・複素 Grassmannian の点を与える。

射影の行列成分から誘導位相を構成し、連続射影族の像として普遍束とその直交補束を構成する。
各点の近傍に連続な正規直交フレームが存在する。
`ProjectiveReal` と `ProjectiveComplex` は階数1に特殊化し、標準線束と直交補束を公開する。
連続な一定階数の射影族から Grassmannian への連続写像を `Family.map` として構成する。
任意の連続写像による普遍束の引き戻しと、合成した射影族の像束との同型を `Pullback.isomorphism` として公開する。
グラフ座標、コンパクト Hausdorff 性、安定化・直和・直交補の写像とそれらの引き戻し比較は未実装である。
既存の `bundle_complements.Projection` は連続な射影族から像束を構成し、`Projection.Pullback` は引き戻しを比較する。
`hermitian_frames` は射影の直交補とブロック和を提供する。
これらと Grassmannian の接続、階数の挙動、座標と位相の証明が残る。

検査と再開方法は `work/b05-resume.md` に記載する。

対象と依存先の検査結果は [検査記録](../../../benchmarks/records/grassmannians/README.md) にある。
