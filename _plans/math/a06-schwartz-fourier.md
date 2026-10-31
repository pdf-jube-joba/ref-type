# A06 Schwartz 空間と Fourier 変換

## 要件

- 主な実装先は `fourier_schwartz`。
- 複素指数関数による Fourier 核、Schwartz 関数の半ノルム、Fourier 変換を構成する。
- 微分・座標乗算・平行移動・畳み込みとの交換、Schwartz 空間の保存を証明する。
- Gaussian の変換と近似単位から Fourier 反転公式を証明し、正規化定数を固定する。

## 依存するタスク

- [A05 Lp 空間のノルムと完備性](a05-lp-completeness.md)
- [G01 滑らかな bump 関数と従属分割](g01-smooth-partitions.md)

## 実装状況

未完了。
`libs/analysis/fourier_schwartz` に複素指数 Fourier 核、実・複素 Schwartz 半ノルム、全ての重み付き偏微分の L1 可積分性、Fourier 変換の滑らかさと Schwartz 保存を構成した。
座標乗算と平行移動の Schwartz 保存、積分下微分による周波数微分公式、平行移動不変性からの部分積分、入力微分公式と平行移動公式を証明した。
Gaussian 自体の Schwartz 性を指数減衰評価と具体的な Hermite 多項式から証明した。
畳み込みとの交換、Gaussian の変換、近似単位による反転公式が残っている。
体系や処理系による不可能性は確認されておらず、残りは数学的実装・証明の作業である。
