# 多様体上の微分形式

大域微分形式、貼り合わせ、引き戻し、De Rham コホモロジーを扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

`Forms[n].On[M].Form(k)` は最大アトラスの全チャートに局所形式を割り当て、重なり上で引き戻しが一致する族である。
`At[k].space`、`Wedge`、`ExteriorDerivative`、`Square`、`Leibniz` は大域形式のベクトル空間と外代数・外微分の法則を公開する。
`Pointwise[k]` は接空間上の滑らかな交代形式の族との双方向の対応であり、`leftInverse` と `rightInverse` は往復の一致を示す。
`DegreeZero` は大域零次形式を滑らかな関数と結ぶ。
大域形式の `Regrade[k, l].cast` も集合値の移送を使い、`chart` は各チャートでの局所形式の移送との一致を示す。

`Pullback[n, m].Between[M, N].Of[f]` は一般の滑らかな写像による引き戻しを構成する。
`At[k].map`、`Product[p, q].law`、`Differential[k].law` は線形性・外積・外微分との整合性を返す。
`PullbackIdentity` と `PullbackComposition` は形式とコホモロジーの恒等則・反変な合成則を示し、`PullbackDiffeomorphism` は両者の同型を返す。
`Restriction` と `Gluing` は任意の開被覆に沿う制限・一意な貼り合わせを公開する。
`Gluing.On.Cover[I, domains].Piece[i]` は被覆の各開部分多様体と、その `Form(k)` を返す。
`At[k, forms].Compatible` は包含写像の微分で共通の接空間へ移した局所形式の一致を表し、`apply` は被覆と互換性の証明から大域形式を構成する。
`AtlasForms` は小さいアトラス上の互換な族を最大アトラスへ一意に拡張し、形式とコホモロジーの同型を構成する。
`Presentation` は同じ最大アトラスを持つ二つの表示を標準的な同型で結ぶ。

`Forms.On.DeRham` は外微分から余鎖複体と商コホモロジーを構成する。
`At[k]` は閉形式・完全形式・類と等式判定を、`Product` とその法則は商の代表によらない次数付きの積を公開する。
`DeRham.DegreeZero.isomorphism` は零次コホモロジーと微分が零になる滑らかな関数の線形同型である。
具体例は [manifolds-de-rham project](../../../tests/projects/manifolds-de-rham/src/root.ref) にある。

```sh
target/debug/cli libs/geometry/differential_forms --module differential_forms --full-check-local --diagnostics compact
```

検査方法と関連パッケージは [ライブラリ一覧](../../README.md) を参照。
