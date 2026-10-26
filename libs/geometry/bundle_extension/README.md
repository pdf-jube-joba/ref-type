# 閉部分空間からの束の延長（B09）

作業中。実数値・複素数値の Tietze 延長は `bundle_extension.Extension.Real.tietze` と `Complex.tietze`。
閉部分空間内の閉集合の像の閉性、Urysohn の分離関数、幾何級数で制御した一様近似列と連続な極限から構成する。

## 追加中の API

- `Real.Components`・`Complex.Components` は任意の成分族を延長する。
- `Real.Matrices`・`Complex.Matrices` は有限矩形行列を成分ごとに延長する。
- `Real.Square`・`Complex.Square` は可逆行列を開近傍へ延長し、`Near` で逆行列の連続性と閉部分空間上の制限式を与える。
- K06 の `Circle.At.domainOff`・`At.Neighborhood.open` は単位円上のスペクトルを避ける領域の開性を与える。
- `Spectral.At.ProjectionRecovery` は複素冪等写像から作る \(2(I-P)\) のスペクトル射影が元の \(P\) に戻ることを証明する。
- `Complex.Spectral` はこの領域へ行列を制限し、K06 のスペクトル射影と像束へ接続する。
- `Complex.Projections`・`Complex.BundleExtension` は閉部分空間上の射影表示を開近傍へ延長し、制限した像束と元の束との比較同型を構成する。
- `Sections.Through`・`RealSections.extend`・`ComplexSections.extend` は有限埋め込み、座標の Tietze 延長、束への射影を組み合わせて切断を延長する。
- `Examples` は一点空間上の実・複素恒等行列に次元0と1で適用する。

## 検証と再開

基点は PR #48 統合済み main `d6ecc14d499efbd782a70ae5c837c4da97c7abc8`。
K07 の `76e6084094f810eaf51e18663bb33d111dd409d7`、K02 の `29f3f43b7a760485ad516dec1c6835d6e09aa41e`、B09 初期実装の `96731109fb2466c72de286aee73ab659e30743a2` が祖先に含まれることを確認した。
継続ブランチは `math/b09-complete-extension`、[PR #49](https://github.com/pdf-jube-joba/ref-type/pull/49) は draft である。
CLI は `source /workspace/ref-type-env.sh` 後の `cargo build -p cli --locked` でビルド済み（終了0）。
共有キャッシュは `libs/refcache`。

| 今回の検査範囲 | module 数 | 終了コード |
| --- | ---: | ---: |
| `bundle_extension.Extension.Real.Components` | 443（19 checked、424 reused） | 0 |
| `bundle_extension.Extension.Real` | 489（44 checked、445 reused） | 0 |
| `spectral_splitting.Spectral.At.ProjectionRecovery` | 609（31 checked、578 reused） | 0 |
| `bundle_extension.Extension.RealSections` | 614（24 checked、590 reused） | 0 |
| `bundle_extension.Extension`（全公開入口・利用例） | 846（46 checked、800 reused） | 0 |

両検査ともキャッシュ保存失敗・worker 復旧・重複・再実行・未保存ステップは0。
レポートは `work/b09-resume/real-components.json` と `real-entry.json`、ログ・レポート・snapshot は追跡しない。
実数値の入口は `beeaefaac7ff31e64e34d2f28a199285f4fa2dd4` までのソースで検証済み。
複素入口の個別検査はレポートが accepted（957 module）だったがシェル終了コードは未取得だったため、後続の全公開入口検査で終了0まで確認した。
`ProjectionRecovery` は `ab5afe450b4649561dbc7bd60281e5fde9dde57f` で型検査が通り、保存失敗・復旧・重複・再実行・未保存ステップは0。
実束の切断の延長は `d803245bb9fc66202020b6a02486428ec0738260` で検証済み（保存失敗・復旧・重複・再実行・未保存ステップ0）。
複素束の近傍への延長・比較、実・複素束の切断、行列の利用例は `7a216d4c8c198cc0a12f78fd740db9275d93d670` の全公開入口検査で検証済み（保存失敗・復旧・重複・再実行・未保存ステップ0）。
実射影の延長で使う `Spectral.Conjugation` は検査待ち。package・workspace 全体の検査も残る。
初回の実成分検査の中断終了130、および宣言順・親参照・型推論の修正前の失敗は上記成功検査で解消した。

残件は実射影表示の近傍への延長と元の実束との比較、束写像・同型の延長、安定化と縮小による比較、自然性、束の具体例、公開 API・登録・ロードマップ・下流リンクと全体検証。
B09 完成・検証・main 統合の後に K03 へ進む。K03 は未着手。
