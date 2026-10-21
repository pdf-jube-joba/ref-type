# A16 楕円 parametrix と正則性

## 要件

- 主な実装先は `elliptic_parametrix`。
- 余接束の零切断の外で可逆な主シンボルから、左右の parametrix を漸近構成する。
- 局所構成を閉コンパクト多様体上で貼り合わせ、左右の誤差が平滑化作用素になることを証明する。
- 楕円評価と分布解の正則性を証明し、滑らかな右辺に対する解の滑らかさを公開する。

## 依存するタスク

- [A14 擬微分作用素の合成と座標変換](a14-symbol-calculus.md)
- [A15 擬微分作用素の Sobolev 有界性](a15-pseudodifferential-bounds.md)
- [A12 束切断の Sobolev 空間](a12-bundle-sobolev.md)
