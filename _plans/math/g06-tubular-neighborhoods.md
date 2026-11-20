# G06 管状近傍と collapse 写像

<a id="status"></a>

## 状況

2026-11-19、main の `dce3d353e75972c507928253d6c33420f6f55a0f` の実コードを読み取りで確認した。
`tubular_neighborhoods` は workspace 登録済みで、40個の `.ref` ファイルがある。
実装は存在するが、以下の確認残があり、計画全体の完了は未確認である。

| 範囲 | 実コードと確認残 |
| --- | --- |
| コンパクト部分多様体 | [Euclidean.On.Of.tubularNeighborhood](../../libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of.ref) と `With.Compact` が法円板近傍を構成し、[Restriction.diffeomorphism](../../libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/With/Restriction.ref) が微分同相を与える。 |
| 境界互換 | [Neat.Crossing.HalfTube](../../libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/Neat/Crossing/HalfTube.ref) に半空間への同相と境界保存がある。[HalfSpace.Of](../../libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/HalfSpace.ref) は `Extension[f]` を入力に要求し、G05 の neat embedding からこの入力を構成する接続は未確認。 |
| 選択とホモトピー | [With.Compare](../../libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/With/Compare.ref) は同じ `lift` の近傍・半径を比較し、埋め込み族と collapse ホモトピーを与える。異なる tubular map の選択まで含む比較の要件対応は未確認。 |
| collapse と積 | [Collapse.Of](../../libs/geometry/tubular_neighborhoods/src/Collapse/Of.ref) に連続性、`Disk.CollapseLaw` に円板内・外の式、[Product.Of](../../libs/geometry/tubular_neighborhoods/src/Product/Of.ref) に `multiplicative` がある。 |
| 安定化 | [Stabilized](../../libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/Stabilized.ref) に `endpointFormula` と積モデルの `suspension` がある。安定化した法束の Thom 空間との同一視を含む比較の完結性は未確認。 |
| 文書・例 | パッケージの README と独立した Examples は未整備。`Line` は構成に使う円板モデル。 |

現行ソースと依存閉包の型検査通過を示す記録は確認できていない。
確認した既存記録の範囲は[ロードマップの検査状況](_roadmap.md#progress-and-checks)に記す。

## 要件

- 主な実装先は `tubular_neighborhoods`。
- Euclid 空間内のコンパクト部分多様体の法束から、零切断の近傍を像の近傍へ送る微分同相を構成する。
- 半空間内の neat embedding に対する境界互換版と、管状近傍の選択を比較する族を構成する。
- 法円板束の外を潰す連続写像を構成し、安定化・積・ホモトピーに関する比較を証明する。

## 依存するタスク

- [G05 コンパクト多様体の埋め込み](../../libs/geometry/compact_embeddings/README.md)
- [滑らかな束・枠束・随伴束](../../libs/geometry/smooth_bundles/README.md)
- [C02 円板束・球面束と Thom 空間](c02-thom-spaces.md)
