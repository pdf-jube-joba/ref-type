# K10 コンパクト台付き K 理論とシンボルの表示

## 要件

- 主な実装先は `compact_support_k`。
- 局所コンパクト Hausdorff 空間について一点コンパクト化による K 群と、コンパクト集合の外で同型となる束の三つ組の群を比較する。
- 円板・球面束の対による表示、台の拡大、開埋め込みによる零延長、proper map による引き戻しを構成する。
- 有限複体による表示、ホモトピー・安定化・直和による等式判定、外積と切除を公開する。

## 依存するタスク

- [K09 Bott 周期性と整数次数](k09-bott-periodicity.md)

## 実装状況

実装中。
`compact_support_k` は一点コンパクト化、整数次数群、proper 引き戻し、開部分空間の零延長、閉対の補空間表示、円板・球面束の比較、外積と切除を公開する。
コンパクト化上のシンボル群には二項束複体、ホモトピー・安定化・直和の関係式と等式判定がある。

`On.BundleTriples.Supported.With` は元の空間上の任意の束とコンパクト集合の外での同型を受け取る。
個々の束の一点コンパクト化への延長は要求しない。
コンパクト近傍への制限で相対三つ組を作り、`On.Localization` によって零延長する。
`Choices.equation` は近傍の選択独立性を証明し、`relative_k_theory.Relative.Pair.BundleTriples` は有限射影表示と負の束の補助束の選択独立性を証明する。
`On.BundleTriples.To.Supported.With` は台の拡大と束同型による表示変更を比較する。
`On.Pullback.BundleTriples.Supported.With.naturality` は proper 引き戻しの自然性を与える。

`With.symbol` と `comparison` は一般の三つ組を既存の小さいシンボル群と一点コンパクト化の K 群へ接続する。
`On.Symbols.Supported.With.Raw.equation` は従来のシンボルを元の空間へ制限して再構成した値が元の類に一致することを示す。
`On.Symbols.RawRepresentatives.existence` は全ての類の一般の束三つ組による代表を与える。
`Examples.Raw` は異なるコンパクト近傍で値が一致する最小利用例である。

一般の有限複体の偶奇和への還元・選択独立性と、元の空間上の一般の束三つ組の生成関係による群表示・加法性・等式判定は実装中。
既存の二項代表と `With.symbol` による値の正規化だけでは、これらの完了とはしない。
