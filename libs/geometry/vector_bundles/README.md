# 実・複素の有限ランクベクトル束

公開入口は `vector_bundles.Bundles`。
`Bundles.Real.scalar` と `Bundles.Complex.scalar` は、[L03](../../algebra/hermitian_frames/README.md) の位相体・共役と、既存の実・複素次元の一意性をまとめる。
`Over[K, field, conjugation, scalar]` の構成はこの共通 API を使う。
線形写像・線形同型・有限基底・trace は [linear_algebra](../../algebra/linear_algebra/README.md) を再利用する。

## 束と局所自明化

`Family[X := X, F := F]` は底の集合 \(X\) とファイバーの集合族 \(F:X\to\mathrm{Set}\) を取る。
`Point` は底点 `base` とベクトル `vector: F base` を持つ依存対で、`include` と `projection` が全空間への挿入と射影である。
`Data` は底空間の位相、全空間の位相、各ファイバーの線形構造を保持し、`Bundle` は局所自明性を満たすデータの型である。

`With[data].ChartData` は開領域、有限次元、領域の各点のファイバーと標準座標の線形同型をまとめる。
`With.In[c].Laws` は底と全空間の領域の開性、局所座標と逆座標の連続性を表す。
`Chart` はその法則を持つ局所自明化である。
`With.In.homeomorphism` は線形同型の逆写像の法則から、全空間の開部分と底の開部分・標準座標の積との同相を作る。

`Of[bundle].projectionContinuous` は局所自明化を貼り合わせて射影の連続性を導く。
`Of.Fiber[x].isomorphism` は射影の実際の逆像と \(F(x)\) の間の線形同型で、`decodeEncode` と `encodeDecode` が両側逆を保証する。

ランクは入力データとして要求しない。
`Dimension.At.basis` はファイバーと標準座標の線形同型から有限基底を構成し、trace による基底の比較とスカラーの自然数埋め込みの単射性で次元の一意性を証明する。
`Of.rank` はその一意な次元、`rankFrame` は局所座標の次元との一致である。
`rankLocallyConstant` は各点の開近傍でランクが一定になることを証明する。
空の底空間、零次元、連結成分ごとに異なる有限ランクを扱える。

## 束写像・束同型・切断

| API | 内容 |
| --- | --- |
| `Over.Morphisms` | 底の写像 \(f:X\to Y\) 上のファイバー線形写像と、その全空間での連続性。 |
| `Morphisms.total` / `projection` / `onFiber` / `ext` | 全空間の写像、射影との可換性、ファイバー上の計算と外延性。 |
| `Morphisms.Composition.compose` / `Over.Identity.map` | 束写像の合成と恒等写像。 |
| `Over.ArrowLaws` / `Associativity` | 単位則と結合則、零切断を用いて束写像から底の写像の連続性を導く証明。 |
| `Over.Isomorphisms` | 同じ底空間上の相互に逆な束写像、全空間の同相と逆の束同型。 |
| `Of.Sections` | 連続な全空間の写像を与える依存ベクトル族としての切断。 |
| `Sections.regular` / `zero` | 局所座標による切断の連続性判定と零切断の構成。 |

## 引き戻しと制限

`Of.Pullback[Y, source, f]` はファイバー \(F(f(y))\) を持つ実際の全空間を作る。
その位相は \(Y\times E\) への自然な埋め込みから誘導し、`pulled[regular]` は \(f\) の連続性から引き戻し束を構成する。
`mapContinuous` は元の全空間への写像の連続性、`In[c].trivialization` は元の局所自明化を引き戻した座標である。

`Universal.Cone` は底と全空間への可換な二つの写像を保持する。
`lift` はファイバーの等式に沿ってベクトルを移送して普遍写像を作り、`baseFormula`、`mapFormula`、`liftContinuous`、`unique` が可換性・連続性・一意性を証明する。
`Pullback.Of.rank` はランクの引き戻し、`Sections.pullback` と `formula` は切断の引き戻しを与える。
`ArrowLaws.Pullback.Of.map` は束写像の引き戻しである。

`Of.PullbackIdentity.isomorphism` と `Of.PullbackComposition.Of.isomorphism` は、恒等写像と合成による引き戻しの比較を実際の束同型として与える。
比較写像は各ファイバーで恒等写像で、二つの誘導位相の間の連続性を普遍性から証明する。
`Of.Restriction[U].restricted` は任意の部分空間への制限で、包含写像に沿う引き戻しとして構成する。
`Restriction.homeomorphism` はその全空間と元の全空間の射影の逆像を、部分空間位相で比較する。

## 構成と利用例

`Over.Trivial[X, n, baseSpace].bundle` は任意の底空間上の自明束で、`homeomorphism` がその全空間と通常の積位相を比較する。
`Over.TwoRanks[n, m].bundle` は離散な二点の底空間上の束を直和位相から構成する。
二つの成分のランクは \(n,m\) で、各成分の局所自明化の両方向の連続性を証明する。

[Examples.ref](src/Bundles/Examples.ref) は実直線上の切断 \(s(x)=x\) を二乗写像で引き戻して \(s(x^2)=x^2\) を計算する。
合成と恒等の引き戻しの束同型、空の底空間の全空間が空であること、零ランク束、ランク0と1を持つ二成分、複素直線束も検査する。

```sh
cargo build -p cli --locked
target/debug/cli libs/geometry/vector_bundles --memory-mib 8192 --cache-stats
target/debug/cli libs --memory-mib 8192 --cache-stats
```

全空間の誘導位相と連続性の普遍性は `topological_constructions.Induced` として公開する。
共有キャッシュを使い、対象・全依存・利用例と、共通の位相構成の変更による workspace への影響を検査する。

対象と全依存の通常検査は最終ソースの38 module・548ソース検査ステップを検査し、依存1,380 module を再利用して成功した。
最大 RSS は約1,033 MiB、worker は1、復旧・重複・再実行・失われたステップ・キャッシュ保存失敗はすべて0であった。
先行する依存閉包の検査でも11,963ソース検査ステップを検査して成功している。
