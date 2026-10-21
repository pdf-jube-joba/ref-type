# A09 Euclid 空間の Sobolev 評価

## 要件

- 主な実装先は `euclidean_sobolev`。
- 整数次数の \(H^s\) を重み付き Fourier ノルムで構成し、非負次数では弱微分による \(W^{k,2}\) と比較する。
- 負次数の双対性、滑らかな関数の乗算、コンパクト台を保つ座標変更の有界性を証明する。
- Sobolev 埋め込みと、全次数の Sobolev 正則性から滑らかさを得る定理を公開する。

## 依存するタスク

- [A07 Plancherel と Fourier 乗算作用素](a07-plancherel.md)
- [A08 分布と弱微分](a08-distributions.md)
- [A04 多重積分の変数変換](a04-change-of-variables.md)
