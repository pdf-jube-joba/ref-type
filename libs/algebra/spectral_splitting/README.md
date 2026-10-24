# 連続なスペクトル分離（K06、実装中）

計画は [_plans/math/k06-spectral-splitting.md](../../../_plans/math/k06-spectral-splitting.md)。
[根群](../complex_polynomial_roots/README.md)、[多項式線形代数](../polynomial_linear_algebra/README.md)、[Hermitian 局所枠](../hermitian_frames/README.md)、[束の補空間](../../geometry/bundle_complements/README.md) を再利用する。

## 検証と再開

基点は main `6bf92837`。
リモートの今回の4単位に対応するブランチと open PR はなく、未完了の各計画が残っていることを確認した。
このコミットは作業開始時点の保存で、数学コードの追加はない。
最新 main の既存実装の検証記録は各依存先の README にあり、今回の新規検査はまだ実行していない。

残作業は単位円の内外の根群・連続射影、Bézout と Cayley–Hamilton による分解と基底変更の自然性、束への貼り合わせ・像の局所自明化・ホモトピー比較、具体例と最終検証である。
次は K05 と L02 の公開 API を接続し、代数的射影と一意性・自然性を実装する。
その後 package/workspace を登録し、`src/USAGE.md` に従って共有キャッシュで対象・依存・影響範囲を検査する。
