# 相対 K 群（K03、実装中）

B09 統合済み main `bd8fd86d5368968ff22e06f81beb5469bc348623` から、`math/k03-relative-k` / [Draft PR #50](https://github.com/pdf-jube-joba/ref-type/pull/50) で実装中。
[計画](../../../_plans/math/k03-relative-k.md)の全要件はまだ完成していない。

## 現在の API

入口は `relative_k_theory.Relative`。
`Pair.Quotient` は一点を付加してから閉部分空間とともに潰し、空の部分空間も同じ定義で扱う。
反復 suspension による負次数群、引き戻し、基点付き同相からの各負次数の比較、開集合を閉部分空間から取り除く切除を提供する。

`Pair.Triple` は二つの射影表示と閉部分空間上の比較同型を持つ。
`Pair.Group` は全体に延長する同型・直和・合成・ホモトピーの関係式による群。
`SumConstruction`・`Normalize`・`FromBundles` は直和、負側の安定自明化、一般の束からの三つ組を構成する。
`Group.Forget` は正負の差を通常の K 群へ送り、`Pair.Restriction` は閉部分空間への制限を与える。
`Group.Forget.Exact` と `Pair.Exact` はこの位置での像と核の一致を示す。

`Descent.descend` は境界上で自明化された束を商へ降ろし、元の束との引き戻し比較と基点のランクを返す。
`FramedClass`・`FramedSum`・`BundleSwitch` は枠付き束の選択独立性、加法性、安定化、ホモトピー不変性、境界同型に沿う交換を構成する。
`Pair.Comparison` は三つ組の群と商の被約群との両方向の準同型と左右の逆の等式を公開し、比較同型の対象検査を完了した。
`Pair.ForgetProjection` は忘却が商への射影による引き戻しに一致することを示す。

`Pointed.Cofiber` は、底面と閉部分空間の円柱の和を潰してコンパクト Hausdorff cofiber を作る。
円錐像の閉埋め込みと収縮、円錐像を潰した商と元の相対商との比較は対象検査済み。

## 未検証の追加

`BaseQuotient` は底面を潰した商と部分空間の suspension を比較する。
明示的な逆写像の連続性を直接示し、点の一意選択は一定の戻り値型を持つ写像の内部へ分けた。
`Connecting`・`Rotation`・`LeftExact`・`FiveTerm` は、基点が部分空間に含まれる対の接続写像、二段の cofiber の変形、五項の群と写像と完全性を構成する。
`SuspendedPair` は suspension の閉埋め込みと、対の商と商の suspension との同相を構成する。
`ClosedPointedPair`・`PointedPair`・`PairIteration` は対を反復し、全体・部分空間・相対商の比較、包含と射影の可換性、各負次数の列と通常の引き戻しとの一致を構成する。
これらの追加は構文解析を通過したが、対象検査は完了していない。

## 検証と再開

共有キャッシュは `libs/refcache`。
以下の固定 snapshot の対象検査は accepted・終了0・キャッシュ保存失敗0。
現在の package・依存閉包・影響先・workspace 全体の最終検証は未実施。
報告・ログ・終了コードは `work/k03-resume` に保存している。

| 範囲 | 報告の接頭辞 |
| --- | --- |
| 三つ組と商の全比較同型 | `reduced-retraction-*` |
| 商の被約群側の忘却・制限の完全性 | `sequence-foundations-Pair-Exact` |
| 負次数の恒等・合成則、定数写像、三つ組の表示 | `sequence-ordered-*` |
| 収縮可能な閉部分空間での忘却の単射性と比較 | `contractible-kernel` / `contractible-forget` / `contractible-comparison-*` |
| コンパクト cofiber と連続な全単射からの同相 | `compact-cofiber-*` |
| 円錐像の閉埋め込み、同相、収縮 | `cone-image-*` |
| 円錐像を潰した商と元の相対商の比較 | `cone-quotient` |
| 枠付き束の降下の引き戻し計算 | `forget-projection-Pair-FramedClass-With-Pullback` |
| 忘却と射影の引き戻しの一致、基点付き被約群の完全性 | `direct-inverse-Pair-ForgetProjection` / `direct-inverse-Pair-Pointed-Exact` |
| 束写像の剪断、交換、直和の並べ替え | `shears-*` / `reordering-*` |

長い `cofiber-exact-…BaseQuotient`・`direct-inverse-…BaseQuotient-Raw`・`constant-raw-…BaseQuotient-Raw` は、構成の整理と計測のため中断した検査。
いずれも終了130・`interrupted`・キャッシュ保存失敗0で、成功した対象検査とは区別する。
最後の中断の後続対象 `Backward`・比較全体は未実行。
計測により、未確定の module 参照から依存範囲が無関係のコホモロジーへ広がっていることを確認した。
`RawMap` の明示 import と `Rotation` 内の兄弟 module の明示参照を追加した。
旧プロセスは終了130・`interrupted`・保存失敗0で回収した。
参照修正後の検査は約64秒でルート宣言のエラーを報告した（終了1・`rejected`・保存失敗0）。
`ClosedPointedPair` の小さい集合への射影が large elimination に該当したため、既存の `CompactPointed` と同じ消去形式で詳細を保持するよう修正した。
空の空間の K 群の消滅と、空の境界での三つ組の忘却の逆写像も追加したが、対象検査は未完了。
`Absolute` は一点付加空間と通常の K 群との比較を、`Pair.Augmented` は一般の対への基点付加と元の相対商との同相を構成した。
これらも構文解析のみ完了し、対象検査は未完了。
次の固定 snapshot で検査を続ける。

```bash
REF_TYPE_PROFILE_DECLARATIONS=1 REF_TYPE_PROFILE_PHASES=1 \
  target/debug/cli libs/topology/relative_k_theory \
  --module relative_k_theory.Relative.Pair.Pointed.Cofiber.BaseQuotient.Raw \
  --memory-mib 14336 --cache-dir libs/refcache --cache-budget-mib 16384 \
  --diagnostics compact --report-json work/k03-resume/closed-pair-raw.json \
  --source-snapshot work/k03-resume/closed-pair-lift.source.json \
  > work/k03-resume/closed-pair-raw.log 2>&1
result=$?
printf '%s\n' "$result" > work/k03-resume/closed-pair-raw.exit
```

`closed-pair-lift.source.json` は `b334fd01` 時点の数学コードの固定 snapshot。
その後の一点付加の構成は `augmentation.source.json` に固定した。
対象検査の完了時は終了コード・JSON の `outcome`・`storage.save_failures`・`checking.cache_write_failures` を確認する。
次に `BaseQuotient.Backward`・`BaseQuotient` の比較全体、新しい五項の列と反復の対象検査を進める。

残る計画要件は、一般の対で通常の K 群を端に持つ負次数の長完全列と自然性、Mayer–Vietoris、外積と自然性、束の円板球面対と具体例。
公開登録・ロードマップ・下流リンクも整備する。
共通 API を整理した K02・K07・単体/胞体・近似理論・B09 の影響先と、workspace 全体を最終検証に含める。
