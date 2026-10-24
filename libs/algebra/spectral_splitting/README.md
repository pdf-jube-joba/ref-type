# 連続なスペクトル分離（K06、実装中）

計画は [_plans/math/k06-spectral-splitting.md](../../../_plans/math/k06-spectral-splitting.md)。
[根群](../complex_polynomial_roots/README.md)、[多項式線形代数](../polynomial_linear_algebra/README.md)、[Hermitian 局所枠](../hermitian_frames/README.md)、[束の補空間](../../geometry/bundle_complements/README.md) を再利用する。

## 検証と再開

基点は main `6bf92837`。
リモートの今回の4単位に対応するブランチと open PR はなく、未完了の各計画が残っていることを確認した。
複素多項式の作用、Bézout 射影・補射影、その独立性、および評価和の右逆を構成した。
基礎4ソースは `ece9322d` で終了コード0（234 module）となった。
`17f58311` の行列版も終了コード0、464 module で受理された。
共通根がない複素多項式の互いに素性の初回検査は公開名の参照で終了コード1となり、修正した。
固定次数の係数族に対する Horner 評価と連続性も追加した。
互いに素性の証明で存在消去の結論の推論が失敗したため、結論を明記した。
`267739bb` の Horner 評価は終了コード0、510 module で受理された。
互いに素性の証明も `742fb3de` で終了コード0、474 module で受理された。
単位円の内外の開性・根因子の分離も `999005ab` で終了コード0となった。
その後の行列式の係数写像、有限係数演算、並び方に依存しない根因子の選択は未検証である。
`c08b33fa` の package 検査は `Coefficients.Data` の大きな除去の制限で終了コード1となった。
有限係数の型を自然数による型の再帰ではなく固定長ベクトルへ変更して再検査する。
作業保存用の [draft PR #42](https://github.com/pdf-jube-joba/ref-type/pull/42) を作成済みである。
最新 main の既存実装の検証記録は各依存先の README にあり、新規範囲の検査は次のコマンドで行う。

```sh
target/debug/cli libs --module spectral_splitting --memory-mib 8192 --diagnostics compact --cache-stats
# 受理済み: --module spectral_splitting.Spectral.At.Families (終了コード0)
# 受理済み: --module spectral_splitting.Spectral.Coprime (終了コード0)
# 受理済み: --module spectral_splitting.Spectral.Circle (999005ab、終了コード0)
# 要再検査: package 全体 (c08b33fa は終了コード1)
```

残作業は単位円の内外の根群・連続射影、Bézout と Cayley–Hamilton による分解と基底変更の自然性、束への貼り合わせ・像の局所自明化・ホモトピー比較、具体例と最終検証である。
次は K05 と L02 の公開 API を接続し、代数的射影と一意性・自然性を実装する。
その後 package/workspace を登録し、`src/USAGE.md` に従って共有キャッシュで対象・依存・影響範囲を検査する。
