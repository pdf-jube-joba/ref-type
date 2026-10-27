# 有限 Grassmannian

B05 の作業中パッケージである。
`Real[n, k].Grassmannian` と `Complex[n, k].Grassmannian` は、それぞれ実・複素の標準 \(n\) 次元空間上の直交射影のうち、像が \(k\) 個の基底を持つものの型である。
射影と階数は `hermitian_frames` の `Projection` と `OnProjection.Rank.HasRank` を再利用する。
`Examples` はゼロ次元の場合の型を参照する。

グラフ座標、位相、コンパクト Hausdorff 性、普遍束、安定化・直和・直交補、射影空間と束の比較は未実装である。
既存の `bundle_complements.Projection` は連続な射影族から像束を構成し、`Projection.Pullback` は引き戻しを比較する。
`hermitian_frames` は射影の直交補とブロック和を提供する。
これらと Grassmannian の接続、階数の挙動、座標と位相の証明が残る。

検査と再開方法は `work/b05-resume.md` に記載する。

対象と依存先の検査結果は [検査記録](../../../benchmarks/records/grassmannians/README.md) にある。
