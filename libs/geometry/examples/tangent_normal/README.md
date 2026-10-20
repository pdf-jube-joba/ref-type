# 接束と法束の利用例

`tangent_bundles` と `normal_bundles` の公開 API を別 package から検査する。
各同型は実際の写像と逆写像、滑らかさと相互逆の証明を持つ。

| module | 内容 |
| --- | --- |
| `Euclidean[n]` | \(T\mathbb R^n\cong\mathbb R^n\times\mathbb R^n\)、接座標による具体的公式、接写像の恒等則 |
| `CoordinateInclusion[n,k]` | \(x\mapsto(x,0)\) の埋め込み性と \((x,a)\mapsto(x,(0,a))\) による法束の自明化 |
| `CoordinateInclusion.Splitting` | 直和分解の実際のベクトル公式と安定化の可換性 |
| `Parabola.Curve` / `Curve.At` | 滑らかな \(t\mapsto(t,t^2)\) と \(v\mapsto(v,2tv)\) の微分公式 |
| `Parabola.At` | 法方向 \((-2t,1)\)、直交条件、任意の法ベクトルの復元 |
| `Parabola.Trivialization` | \((t,a)\mapsto(t,a(-2t,1))\) による一般構成の法束との微分同相、逆は第二周囲座標 |
| `Parabola.Trivialization.addition` / `scaling` | 公開される法束のファイバー演算の具体的な利用 |
| `Parabola.Functor` | 放物線と第一座標射影の接写像の合成、直和分解、安定化 |
| `Empty[n,k]` | 空多様体からの実際の滑らかなはめ込み、接束と法束の全空間が空であること |
| `Degenerate` | 零次元ユークリッド空間の接束、余次元零の法ベクトルの零性、\(n=k=0\) |

放物線の第一座標射影は滑らかな左逆写像であり、`manifolds.EmbeddingRetraction` から埋め込みを得る。
`Parabola.At.reconstruction` は直交条件だけから \(w=w_2(-2t,1)\) を証明する。
`Trivialization` は正規化を必要としないこの大域枠を用い、一般構成の正規直交局所枠で与えた全空間への滑らかさを `FromAmbient` で示す。
有限次元の添字を使うため、実数パラメータは一座標ベクトルの標準線形同型 `CoordinateLine` を介して表す。

検査はリポジトリのルートで実行する。

```sh
cargo build -p cli --locked
target/debug/cli libs/geometry/examples/tangent_normal --cache-dir libs/refcache --memory-mib 7168 --diagnostics compact
```

通常検査はこの package と依存閉包のすべての module を対象にする。
