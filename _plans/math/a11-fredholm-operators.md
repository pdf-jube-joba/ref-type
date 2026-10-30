# A11 Fredholm 作用素と指数

## 要件

- 主な実装先は `fredholm_operators`。
- コンパクト作用素のイデアルと Atkinson の定理を証明し、parametrix の存在と Fredholm 性を同定する。
- 核・余核の有限次元性、指数の合成則・直和則・コンパクト摂動不変性・ノルム連続な族での局所定数性を証明する。
- 実際の核・像・余核と有限次元の分解から指数を計算できる API を公開する。

## 依存するタスク

- [A19 複素 Hilbert 空間とコンパクト作用素](a19-complex-hilbert.md)

## 完了状況

全要件を実装・検査済み。
実装ソースは `58f20c30015fd6d343ff3f77f8dcc7ec1240afc0` である。

| 要件 | 状況・公開 API |
| --- | --- |
| コンパクト作用素のイデアル、Atkinson の同値 | 完了。`Operators.Ideal`、`At.Hilbert.atkinsonEquivalence` |
| 核・余核の有限次元性 | 完了。実際の `kernel`、`image`、商 `CokernelSpace` を使用する |
| 指数の合成則・直和則 | 完了。`At.Composition.Hilbert.indexComposition`、`At.Hilbert.DirectSum.At.indexDirectSum` |
| コンパクト摂動不変性・ノルム連続族の局所定数性 | 完了。`CompactPerturbation.indexInvariant`、`indexLocallyConstant`、`Operators.Hilbert.Family.At.locallyConstant` |
| 実際の有限次元分解からの計算、最小例、文書 | 完了。`At.Index.Decomposition`、`indexFromDecomposition`、`Examples.indexZero`、公開 README |

A11 全体、隔離キャッシュの具体例、A19 回帰は成功した。
標準 `cargo build -p cli --release --locked && python3 scripts/check_all.py` も終了コード 0 で 9,887/9,887 対象を検証し、未検証・保存失敗は 0 だった。
実装・検査ソースとの対応、所要時間、キャッシュ条件、過去の失敗記録は [検査記録](../../benchmarks/records/fredholm-operators/README.md) にまとめる。
