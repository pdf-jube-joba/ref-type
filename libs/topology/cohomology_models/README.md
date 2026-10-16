# 特異コホモロジーの利用例

`singular_cohomology` の公開 API を別パッケージから検査する。

| module | 検査する内容 |
| --- | --- |
| `Basic` | 定数特異単体、代表余鎖の値、鎖・余鎖の二乗の零性、増大複体の次数 \(-1\)、増大の右逆、空空間・一点・区間の計算、道成分による零次の表示、被約ホモロジーの負一次の規約。 |
| `Relative` | 部分空間の鎖が商で零になること、相対微分の二乗の零性、係数付き相対群、長完全列の接続写像と完全性、部分空間で零になる余鎖との同型、余鎖の短完全列とコホモロジー長完全列。 |
| `Coefficients` | 係数短完全列からの Bockstein 接続写像と完全性。 |
| `OpenCovers` | 一点空間での切除の群同型と、開被覆の鎖・余鎖短完全列、通常の特異理論の Mayer–Vietoris 列。 |
| `Maps` | 連続写像が鎖の生成元に誘導する写像、係数付き余鎖写像の代表元での評価と恒等写像のコホモロジーでの作用。 |
| `Geometry` | 任意次元のユークリッド円板の可縮性による計算と、ユークリッド球面 \(S^0\) と離散二点空間の同相。 |
| `ZeroSphere.With` | 二つの一点開集合の Mayer–Vietoris 比較による \(H^0(S^0;M)\cong M\oplus M\) と正次数の零性。 |

```sh
target/debug/cli libs/topology/cohomology_models --module cohomology_models --diagnostics compact
```

依存先と共通の `libs/refcache/` を利用する。
