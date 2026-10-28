# 相対 K 群と負次数の完全列

コンパクト Hausdorff 空間と閉部分空間の対に対して、束の三つ組による相対群と一点付加商の被約 K 群を比較する。
入口は `relative_k_theory.Relative`。
三つ組と商の比較、負次数の完全列、切除、Mayer–Vietoris、外積、束の円板・球面対を公開する。

## 群と比較

`Pair` の引数は空間 `X`、位相 `space`、コンパクト性 `compact`、Hausdorff 性 `hausdorff`、閉部分空間 `subset` と `closed`。
`Pair.Triple` は二つの射影表示と部分空間上の束同型、`Pair.Group` は延長可能な同型・直和・合成・ホモトピーの関係による群を与える。
`FromBundles`・`SumConstruction`・`Normalize` は一般の束の表示、直和、負側の安定自明化を構成する。

`Pair.Quotient` は空間へ基点を付加し、基点と閉部分空間を一緒に潰す。
空の部分空間も同じ構成で扱う。
`Pair.Comparison` は三つ組の群とこの商の被約群との加法的比較、および左右の逆を与える。
`Descent`・`FramedClass`・`FramedSum`・`BundleSwitch` は境界の自明化からの束の降下と、選択独立性・加法性・安定化・ホモトピー不変性を構成する。
`Pair.Mapping.Group` は比較を通じて三つ組の群の引き戻しを与え、加法・零元と比較の自然性を公開する。

## 負次数、完全列と自然性

`Negative[original, degree]` は反復 suspension の被約群として負次数を定義する。
`NegativeMap`、`PullbackIdentity`、`PullbackComposition`、`HomotopyInvariance` は引き戻しと恒等・合成・ホモトピーの法則を与える。
`Absolute` は一点付加した空間の零次数群と通常の K 群を比較する。

`Pair.Augmented.Sequence[degree := n]` は
\[
K^{-(n+1)}(X)\longrightarrow K^{-(n+1)}(A)\longrightarrow K^{-n}(X,A)
\longrightarrow K^{-n}(X)\longrightarrow K^{-n}(A)
\]
の四つの写像と各内部項での像と核の一致を公開する。
`restrictionNegative`・`boundary`・`forget`・`restriction` は加法的で、`exactSecond`・`exactThird`・`exactFourth` が完全性を表す。
`Pair.Augmented.OrdinaryEnd` は次数0の端を通常の K 群の忘却・制限へ比較する。
`Pair.Mapping.Augmented.Negative` は一般の閉対の写像に対する接続・忘却・制限の自然性を与える。
基盤の `PairIteration`・`PairMapping.Iteration` は対を反復し、全体・部分空間・商の suspension 比較と写像の可換性を構成する。

## 切除と Mayer–Vietoris

`Pair.Excision` は閉部分空間に含まれる開集合を取り除いた対と元の対の商を、明示的な連続逆写像によって比較する。
各負次数の比較は `Excision.Negative`。
`Pair.ClosedCover[V, closedV, covers]` は二つの閉部分空間が全体を覆う場合の商比較を与え、開集合による切除を補集合の閉被覆として扱える。

`ClosedCover.MayerVietoris[degree]` は接続写像、二片への制限、交叉への制限の差を構成する。
`exactWhole` は全体の群での完全性、`Positive` は以降の二位置の完全性を与える。
`MayerVietorisZero.exactPieces` は次数0で二片上の類の貼合せを与える。
`ClosedCover.Mapping.Negative` は被覆を保つ写像に対する切除比較・制限・差・接続の自然性を公開する。

次数0の貼合せは `ClosedCover.Patching` にある。
交叉上の束同型から二方向の矩形写像を作り、B09 の Tietze 延長、可逆な剪断、閉被覆上の冪等写像の貼合せ、像束の構成を使う。
`Patching.Ordinary.existence` は K01 の安定同型判定と仮想束の正規形を使い、両側の制限式を満たす通常の K 群の類を返す。

## 外積

`Smash` は積空間の二軸を潰したコンパクト Hausdorff 空間を構成する。
`Smash.External` は零次数外積を一意な相対持ち上げとして構成し、双加法性と零元の式を与える。
`Smash.Suspension`・`Symmetry`・左右の反復比較から `Smash.Graded` が負次数外積を構成する。
比較同相は共通のコンパクトな代表空間上のファイバーの一致から作り、自然性を実際の代表写像で証明する。

二つの閉対には `Pair.Product` を使う。
境界は \(A\times Y\cup X\times B\) で、その相対商と二つの相対商の smash を比較する。
`External` と `Negative[firstDegree, secondDegree]` はこの比較を通じた外積、`Pullback.External` と `Pullback.Negative` はその自然性を与える。
負次数の結果の次数は `secondDegree + firstDegree`。

## 束の円板・球面対と利用例

`DiskPair[p]` は射影表示からコンパクトな円板とノルム1の閉境界、相対群を構成する。
`BundleDisk.existence` は任意のコンパクト束にその表示を与える。
表示 `r` を選んだ `BundleDisk.With[r]` は元の束への連続単射とノルム条件を公開し、`OriginalUnit.homeomorphism` は元の束の単位円板との同相、`sphereEquation` は球面条件の一致を与える。
したがって円板・球面対を一般の閉対の列・外積へ渡せる。

`Examples.TrivialDisk[n]` は一点上のランク `n` の自明束で、円板の座標表示との明示的な同相 `diskHomeomorphism` を構成する。
ランク0・1は package の検査範囲に登録されている。

```ref
\import std.Data[].Nat[] \as Nat;
\import relative_k_theory.Relative[].Examples[] \as Examples;
\import Examples.TrivialDisk[n := Nat.Nat^::zero] \as Zero;
\import Examples.TrivialDisk[n := (Nat.Nat^::succ Nat.Nat^::zero)] \as Line;
```

`Zero.Disk`・`Line.Disk` は円板、`Zero.Relative`・`Line.Relative` は対応する相対群。
`Examples.zeroBoundaryEmpty` はランク0の球面境界が空であることを示す。

## 検証

共有キャッシュ `libs/refcache` を使用する。
三つ組と商の比較、一般の対の完全列、写像の自然性、smash と閉対の外積、閉被覆の貼合せと Mayer–Vietoris、元の束の単位円板との同相、ランク0・1の利用例を対象と依存閉包で検査した。
いずれも accepted・終了0・キャッシュ保存失敗0・書込失敗0。

2026-10-28 の最終 workspace 全体検査も9,048モジュールで accepted・終了0・キャッシュ保存失敗0・書込失敗0を確認した。
308モジュールを検査し、内容の一致する8,740モジュールを共有キャッシュから再利用した。
K03 全体、全依存、共通補題の移動による影響先、利用例を含む。
worker 1・自動復旧0・重複0・再実行0・未保存0で、約1,384秒。
物理メモリ上限16 GiBの環境で、最大 RSS は14,399,064 KiB。

検査した数学ソースのリモート commit は `ad55f6f4243e6bc060ec74ef48af363f7a23abc9`、tree は `3ecfdb61538c923656af74f55d283d3cf15de754`。
main `f8b80a154a3b61d2dccebd0ea13adc44bfaa4bdb` の変更を保持し、Grassmannian の分離補題への参照も共通 API の移動先へ合わせている。
報告は `work/k03-resume/workspace-audit-15.{log,json,exit}`、固定入力は `workspace-audit-12.source.json` に保存した。
固定入力7,942ファイルと検証後の数学ソース・manifest の一致も確認した。
以前の中断・資源上限による終了の報告も同じディレクトリに保持している。

リポジトリ直下からの通常検査は次のとおり。

```sh
MIMALLOC_ARENA_RESERVE=64M REF_TYPE_GRAPH_RESIDENT_MIB=256 target/debug/cli libs \
  --cache-dir libs/refcache --cache-budget-mib 16384 --memory-mib 0 \
  --checkpoint-seconds 600 --diagnostics compact
```

固定入力の保存と検査方法は [検査とキャッシュ](../../../src/USAGE.md#検査とキャッシュ) を参照。
