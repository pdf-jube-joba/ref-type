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

全要件の構成と証明を `libs/analysis/fourier_schwartz` に実装した。
複素指数 Fourier 核、実・複素 Schwartz 半ノルム、全ての重み付き偏微分の L1 可積分性、微分・座標乗算・平行移動・畳み込み公式、Schwartz 保存、Gaussian の Fourier 公式、Gaussian 近似単位による反転公式を含む。
正規化は Gaussian 積分で構成した定数を用いる \((2\pi)^{-n}\) であり、Schwartz 値の逆写像の左右の逆恒等式も証明した。
最終ソースに対する対象検査・依存回帰・通常全体検査の記録は `benchmarks/records/a06-fourier-schwartz` に保存する。
