# C01 作業メモ

ブランチ `codex/c01-cap-products` は C01 の特異 cap 積を実装する。
`Integral.At` に整数鎖の生成元上の構成がある。
整数係数の標準整数作用と乗法の一致、および任意の鎖における cup–cap 評価の随伴を検査済み。
鎖の自然性と Alexander–Whitney 分解を利用した境界公式も通常検査済み。
次に相対積、切除と長完全列、外積、射影公式と相対自然性を構成する。
通常検査は `libs/refcache` を共有する。

相対 cap の部分空間保存を検査済み。`Integral.Pair.At.Quotient` の商への降下を検査中。
