# A01 作業メモ

基準は main `bd8fd86d`、作業ブランチは `codex/a01-measure-convergence`。
既存 `libs/refcache` と `target/debug/cli` を共有して通常検査を実行する。
`functional_analysis.Measure.Integral` の単調性、有限性の下方継承、積分値の一意性は検査済み。
依存順序は、可測集合と測度の有限演算、非負拡張実数の演算、単関数の分割と積分、下積分の加法性と近似、単調収束、Fatou、優収束、符号付き積分の線形性と a.e. 同値、複素・有限次元ベクトル値および級数との交換である。
各段階は狭い通常検査で確認し、区切りと長い検査の前に commit と push を行う。
