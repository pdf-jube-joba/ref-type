# 閉部分空間からの束の延長（B09）

コンパクト Hausdorff 空間 \(X\) の閉部分空間 \(A\) から、実・複素の関数、束、束写像、束同型を延長する。
束は \(A\) を含む開近傍へ延長し、元の束との制限比較同型も構成する。
空の部分空間、次元0、連結成分ごとに階数が異なる束を排除する仮定は置かない。

## 公開 API

入口は `bundle_extension.Extension`。
`Real`・`Complex` の引数は底集合 `A`、底位相 `source`、閉部分集合 `subset` である。

| API | 内容 |
| --- | --- |
| `Real.tietze`・`Complex.tietze` | 実数値・複素数値の連続関数を \(X\) 全体へ延長 |
| `Real.Components`・`Complex.Components` | 任意の添字集合による成分族の延長 |
| `Real.Matrices`・`Complex.Matrices` | 有限矩形行列族の成分ごとの延長 |
| `Real.Square`・`Complex.Square` | 可逆行列の開近傍への延長、連続な逆行列と制限式 |
| `RealProjections`・`Complex.Projections` | 冪等行列族の開近傍への延長、像束と制限比較 |
| `RealBundleExtension`・`Complex.BundleExtension` | 任意の有限階数束の近傍への延長 |
| `Sections`・`RealSections.extend`・`ComplexSections.extend` | \(X\) 上の束の閉部分空間上の切断を \(X\) 全体へ延長 |
| `RealMaps.extend`・`ComplexMaps.extend` | \(X\) 上の二束間の閉部分空間上の束写像を \(X\) 全体へ延長 |
| `RealIsomorphisms.extend`・`ComplexIsomorphisms.extend` | 閉部分空間上の同型を開近傍上の同型へ延長 |
| `RealLocalIsomorphisms.extend`・`ComplexLocalIsomorphisms.extend` | 開近傍上の二束の同型を、より小さい共通開近傍へ延長 |
| `CompactNeighborhood` | 開近傍内にコンパクトな閉近傍を取り、相対開近傍を \(X\) の開近傍へ持ち上げる |

`RealMaps`・`ComplexMaps` は共通の底位相 `baseSpace` と `sourceSame`・`same` で束の底位相との一致を受け取る。
通常は `baseSpace := source.baseSpace`、`sourceSame := \refl(source.baseSpace)` とする。
束の延長の `Witness` は有限射影表示と行列の延長を保持し、`With` は `domain`・`open`・`contains`・`Fiber`・`extended`・`restricted`・`comparison` を公開する。
同型の延長の `Result` は開近傍、連続な逆写像を持つ同型、閉部分空間上で与えられた同型と一致する式を保持する。

## 構成

実数値 Tietze は、正規性から得る Urysohn 関数と、幾何級数で誤差を抑えた一様近似列の連続な極限から作る。
複素数値の場合は実部と虚部に適用する。
成分族・矩形行列の延長では、各成分の延長を選んで連続性と制限式をまとめる。

束には [B03 の有限埋め込みと射影表示](../bundle_complements/README.md)を使う。
冪等写像 \(P\) に対する \(2(I-P)\) のスペクトルは0と2に分かれ、[K06 のスペクトル射影](../../algebra/spectral_splitting/README.md)で元の \(P\) を回復する。
行列の延長後、単位円上のスペクトルを避ける開領域へ制限して像束を得る。
実束では実行列を複素化し、共役を保つスペクトル射影を実座標へ戻す。
`RealLinear` が複素化・制限・行列積・射影回復の整合性を証明する。

束写像には、両束の有限埋め込みとレトラクションを使う。
閉部分空間上の写像を矩形行列に符号化し、成分を延長して束へ射影し直す。
同型の場合は順写像と逆写像を延長し、二つの合成が可逆になる共通開近傍へ制限する。
`Over.Endomorphisms` は、束の自己写像を自明束の補束上で恒等写像に拡張し、行列式の非零領域と連続な逆行列から逆写像を構成する。

## 延長の比較と相対三つ組

二つの束の延長は、定義域を共通開近傍へ制限し、閉部分空間上での比較同型を合成して `RealLocalIsomorphisms` または `ComplexLocalIsomorphisms` に渡す。
`extend` は、指定した比較同型と一致する同型を、さらに小さい開近傍上で構成する。
開近傍自体のコンパクト性は要求せず、`CompactNeighborhood` の閉近傍へ制限してから延長を戻す。
相対 K 理論の三つ組 \((E,F,\alpha)\) の閉部分空間上の同型 \(\alpha\) にもこの入口を使える。

`Over.Isomorphisms.With.Pullback` は指定された延長同型を引き戻し、反復引き戻しを一段の引き戻しと比較する。
`With.Stabilize[n]` は自明な \(n\) 次元束との直和を取り、閉部分空間上で \(\alpha\oplus\mathrm{id}\) に一致する式を与える。
縮小比較にも `Over.LocalIsomorphisms.With.Stabilize[n]` を用いる。
束の延長の `With.Pullback` は、元の閉部分空間への連続写像に沿って、元の束と延長束の制限比較同型を引き戻す。
いずれも指定した延長を運ぶ構成であり、存在証明で選ばれる延長の一意性は要求しない。

## 利用例

`Examples.RealBundle`・`ComplexBundle` は一点空間上の実・複素自明束を延長し、次元0と1で実体化する。
`Examples.Mobius` は \(S^1\times[0,1]\) の閉端面 \(S^1\times\{0\}\) 上の Möbius 束を開近傍へ延長する。
`Examples.ComplexLine` は \(S^2\times[0,1]\) の閉端面上の、[B04 の単位円遷移による複素線束](../bundle_homotopy/README.md)に同じ構成を適用する。
`Examples.EmptyRealBundle`・`EmptyComplexBundle` は、空の閉部分空間からの束の延長を実体化する。
行列についても実・複素の恒等行列を次元0と1で検査する。

## 検証と再開

基点は PR #48 統合済み main `d6ecc14d499efbd782a70ae5c837c4da97c7abc8`。
K07 の `76e6084094f810eaf51e18663bb33d111dd409d7`、K02 の `29f3f43b7a760485ad516dec1c6835d6e09aa41e`、B09 初期実装の `96731109fb2466c72de286aee73ab659e30743a2` は祖先に含まれる。
継続ブランチは `math/b09-complete-extension`、[PR #49](https://github.com/pdf-jube-joba/ref-type/pull/49) を使う。

`0c694eafc0e4d9fd49180704195e6977571a8bb0` の全公開入口は764 module（173 checked、591 reused）、キャッシュ保存完了・終了0。
実・複素の束・束写像・同型、開近傍上の比較、自然性・安定化、閉端面上の線束の例を含む。
worker 復旧・重複・再実行・未保存ステップ・保存失敗は0。
空の閉部分空間の利用例を加えた実装の保存先は `fb8cc1a36a3f343e4e88fbd44ae75790e5c8567f`。
このソースの package・依存閉包を、固定 snapshot `work/b09-resume/package-final.source.json` と共有キャッシュ `libs/refcache` で検査中である。
workspace 全体の検査と最終差分確認は未完了で、PR は draft のままである。
K03 は B09 の検証・main 統合後に着手する。

再検査はリポジトリルートから行う。

```sh
target/debug/cli libs/geometry/bundle_extension --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --cache-stats --diagnostics compact --report-json work/b09-resume/package.json
target/debug/cli libs --memory-mib 10240 --cache-dir libs/refcache --cache-budget-mib 12288 --cache-stats --diagnostics compact --report-json work/b09-resume/workspace.json
```

CLI は `cargo build -p cli --locked` でビルド済み（終了0）。

検査開始後、`Over.Idempotents` の末尾の余分な空行を整えた。
固定 snapshot の検査後、現在のソースとの一致を改めて確認する。
