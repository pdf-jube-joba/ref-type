# 鎖複体と余鎖複体

環上の自然数・整数次数の複体、ホモロジー、写像とホモトピーを扱う。

| module | 内容 |
| --- | --- |
| `Cochain.Over` | 自然数次数の余鎖複体、サイクル・境界の商、誘導写像 |
| `Integer.Over` | 整数次数の余鎖複体 |
| `Cochain.Over.ZeroExtension` / `Recovery` | 負次数を零にする拡張と制限の往復、コホモロジー同型 |
| `Chain.Over.At` / `Map.At` | 整数次数の鎖複体、ホモロジーと誘導写像 |
| `Chain.Over.Homotopy` / `Equivalence.At` | \(f-g=dh+hd\)、ホモトピー同値による同型 |
| `Chain.Over.Shift` / `Cone` / `ConeIdentity` | 符号 \(-d\) のシフト、mapping cone、恒等写像の cone の収縮 |
| `Chain.Over.Zero` / `Concentrated` / `ZeroDifferential.At` | 零複体、単一次数、零微分のホモロジー |
| `Chain.Over.Map.Kernel` | 項ごとの核、全射な比較写像の核の完全性から得るホモロジー同型 |
| `Chain.Over.QuotientMapping.On` | 可換な正方形が誘導する商複体の写像と生成元での公式 |
| `Chain.Over.ShortExact.Morphism.Diagram` / `Integer.Over.ShortExact.Morphism.Diagram` | 長完全列の自然性と五項完全列による相対群の比較 |
| `Chain.Over.Reverse` / `Reversal.Over.ToChain` | 次数の符号反転による鎖・余鎖の変換 |
| `ModuleCategory.Over.On` / `ShortExactCategory.Over.On` | 加群族の前加法圏、短完全列の圏と接続写像の自然性 |
| `CochainEquivalence.Over.Of.With` | 余鎖ホモトピー同値によるコホモロジー同型 |

次数零の余鎖境界は零部分加群とする。
零拡張の `PositiveCohomology`・`NegativeCohomology` は元のコホモロジーとの同型・負次数の消滅を返す。
体係数の分裂と収縮は [field_kunneth](../field_kunneth/README.md) にある。
