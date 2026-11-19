# A09 Euclid 空間の Sobolev 評価

<a id="status"></a>

## 状況

2026-11-19、main の `dce3d353e75972c507928253d6c33420f6f55a0f` の実コードを読み取りで確認した。
`euclidean_sobolev` は workspace 登録済みで、[README](../../libs/analysis/euclidean_sobolev/README.md) と31個の `.ref` ファイルがある。
README の存在に加えて以下の実装を確認したが、計画全体の完了は未確認である。

| 範囲 | 実コードと確認残 |
| --- | --- |
| Fourier モデルと双対性 | [Signed](../../libs/analysis/euclidean_sobolev/src/Euclidean/Signed.ref) と `Order` に整数次数のモデル、[Order.Duality](../../libs/analysis/euclidean_sobolev/src/Euclidean/Order/Duality.ref) にペアリング・評価・有界汎関数の一意な表現がある。 |
| 弱微分との比較 | [Weak.ofSchwartz](../../libs/analysis/euclidean_sobolev/src/Euclidean/Weak.ref) は実 Schwartz 関数を弱微分の空間へ送り、[Energy.comparison](../../libs/analysis/euclidean_sobolev/src/Euclidean/Energy.ref) は複素 Schwartz 関数上のノルムを比較する。`Order.Density.sequenceExists` は近似列を与えるが、一般の \(H^k\) と \(W^{k,2}\) の双方向比較までの要件対応は未確認。 |
| 乗算と座標変更 | [Transport](../../libs/analysis/euclidean_sobolev/src/Euclidean/Transport.ref) はコンパクト台の係数を伴う引き戻しと零延長を正負次数で与える。[MultiplicationBy](../../libs/analysis/euclidean_sobolev/src/Euclidean/MultiplicationBy.ref) は実数値の滑らかなコンパクト台関数を入力とする。計画の「滑らかな関数の乗算」に必要な係数クラスとの対応は確認残。 |
| 埋め込みと滑らかさ | [EmbeddingTheorem.theorem](../../libs/analysis/euclidean_sobolev/src/Euclidean/EmbeddingTheorem.ref) は \(2p>n\) で \(H^{r+p}\) の \(C^r\) 代表を構成し、[Regularity.smooth](../../libs/analysis/euclidean_sobolev/src/Euclidean/Regularity.ref) は全非負次数に属する元の共通の滑らかな代表を与える。 |
| 利用例 | 独立した Examples は確認できていない。 |

現行ソースと依存閉包の型検査通過を示す記録は確認できていない。
確認した既存記録の範囲は[ロードマップの検査状況](_roadmap.md#progress-and-checks)に記す。

## 要件

- 主な実装先は `euclidean_sobolev`。
- 整数次数の \(H^s\) を重み付き Fourier ノルムで構成し、非負次数では弱微分による \(W^{k,2}\) と比較する。
- 負次数の双対性、滑らかな関数の乗算、コンパクト台を保つ座標変更の有界性を証明する。
- Sobolev 埋め込みと、全次数の Sobolev 正則性から滑らかさを得る定理を公開する。

## 依存するタスク

- [A07 Plancherel と Fourier 乗算作用素](../../libs/analysis/fourier_l2/README.md)
- [A08 分布と弱微分](../../libs/analysis/distributions/README.md)
- [A04 多重積分の変数変換](../../libs/analysis/change_of_variables/README.md)
