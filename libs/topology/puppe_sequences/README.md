# CW cofibration と Puppe 列（K02）

入口は `puppe_sequences.Puppe`。
円板境界と有限 CW 部分複体のホモトピー拡張性、基点付き cofiber の反復、reduced suspension との比較、基点固定ホモトピー類の反変 Hom の完全性を提供する。

## 公開 API

| API | 内容 |
| --- | --- |
| `Cofibration.fromExtension` | 既存のホモトピー拡張性から cylinder の貼り合わせへの retraction を構成 |
| `Disk.Boundary.cofibration` | 任意次元の閉円板の境界包含が cofibration |
| `CW.Subcomplex.cofibration` | 有限 CW 部分複体の包含が cofibration。セル境界の拡張と骨格の帰納法で証明 |
| `Maps` | 基点を固定するホモトピーとその商集合、前合成・後合成 |
| `ReducedCone`、`Cone`、`Suspension` | 基点付き円錐・mapping cone・reduced suspension と連続な誘導写像 |
| `Cone.Exactness.exact` | \([C_f,Z]\to[B,Z]\to[A,Z]\) の核と像の一致 |
| `Cone.Connecting`、`Cone.Morphisms.Of` | 接続写像と、対の可換図式が誘導する写像・自然性 |
| `Cone.Iteration.Inverse.equivalence` | \(C_{B\to C_f}\simeq\Sigma A\)。比較射影・逆・基点固定の両側ホモトピーを構成 |
| `Cone.Iteration.Successor.homotopy` | 次の接続写像と、区間の時間反転を伴う \(\Sigma f\) の比較 |
| `Cone.Iteration.Exactness.exact` | \([\Sigma A,Z]\to[C_f,Z]\to[B,Z]\) の完全性 |
| `Pair.equivalence` | cofibration に対する mapping cone と商空間の比較写像のホモトピー同値 |
| `CW.Subcomplex.Pointed.equivalence` | 基点を含む有限 CW 部分複体への商比較の適用 |
| `Sequence.Of.At` | 自然数で反復した cofiber 列の各段、suspension との比較、`Hom.exact` と `Hom.connectingExact` |
| `Sequence.Natural` | 対の写像から各段の可換図式を帰納的に構成 |
| `Equivalence.Contravariant` | ホモトピー同値が反変ホモトピー類に誘導する両側逆 |

`Sequence.Arrow` は基点付き写像をまとめる。
`Sequence.pack` に二つの台集合と `Sequence.Details` を渡し、`Sequence.Of` で列を作る。
第0段は与えた写像、第1段は mapping cone への包含、第2段の終域は元の始域の suspension と比較される。
各段で同じ比較を反復でき、`successorComparison` が次の写像の時間反転を明示する。
この向きの規約は、円錐の底面を区間の0、頂点を1とする定義による。

`Pair.equivalence` は既存の `algebraic_topology.Cofibration.IsCofibration` を受け取り、指定の比較写像を前向き写像に持つ同値の存在を返す。
逆写像はホモトピー拡張から構成し、存在を仮定しない。

## 例と検査

`Examples.intervalBoundary` と `Examples.planeBoundary` は1次元・2次元円板の境界包含を検査する。
`Examples.identityComparison` と `Examples.constantComparison` は二点離散空間の恒等写像・定数写像からの反復比較であり、`identityOnClasses` と `constantOnClasses` は実際のホモトピー類上の作用を確認する。

```sh
target/debug/cli libs/topology/puppe_sequences --module puppe_sequences.Puppe --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact
target/debug/cli libs --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --diagnostics compact
```

依存する共通 API として `topological_constructions.Quotient.Descent`、`Coproduct.ProductUniversal`、`Pushout.Of.Families`、`RelationQuotient.Families` を追加した。
積と商の交換にはコンパクト Hausdorff な区間を使う。
[相対 K 群の K03](../../../_plans/math/k03-relative-k.md) はこの列と有限 CW 対の比較を利用する。

## 保存・再開

基点は K07 統合済み main `76e6084094f810eaf51e18663bb33d111dd409d7`。
作業ブランチは `math/k02-cofibration-puppe`、[PR #47](https://github.com/pdf-jube-joba/ref-type/pull/47)。
公開入口・依存閉包・例は `puppe-public.json` で accepted・終了0・保存失敗0。
反復列の完全性・自然性と次の接続写像の比較まで実装・検査済み。
実装の保存済みリモートは `29fc8e5490ef3cb4deaab6f9011e7e0b26c0b1e3`（以後の検査記録更新は PR head を参照）。
workspace 全体は `workspace-final.json` で1200秒上限に達し、time-limit・終了2・保存失敗0。
最後の検査箇所は `uniform_approximation.Approximation.On.AlgebraEvaluation.At`、終了時の未完了 step は535。
全体検査は未完了なので PR は draft、main は未変更。
同じ共有キャッシュで workspace 検査を再開し、accepted・終了0・保存失敗0を確認してからロードマップ・下流リンク、PR の ready・merge・main 反映確認へ進む。
共有キャッシュは `libs/refcache`。
