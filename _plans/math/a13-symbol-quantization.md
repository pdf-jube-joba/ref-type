# A13 シンボルと局所量子化

## 要件

- 主な実装先は `pseudodifferential_symbols`。
- Euclid 開集合上の行列値シンボル \(S^m_{1,0}\) と古典的な斉次展開を定義し、微分の評価を証明する。
- 振動積分を cutoff 極限として構成し、proper support を持つ量子化作用素を試験関数・分布に作用させる。
- 平滑化作用素、主シンボル、微分作用素との一致、漸近級数の実現を公開する。

## 依存するタスク

- [A06 Schwartz 空間と Fourier 変換](a06-schwartz-fourier.md)
- [A08 分布と弱微分](a08-distributions.md)
