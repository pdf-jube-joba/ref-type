# ホモロジー代数の具体例

| module | 確認する構成 |
| --- | --- |
| `BasicComplexes` | 零複体、集中した加群、恒等写像の cone と符号 |
| `Cyclic` / `Extensions` | \(\mathbb Z/2,\mathbb Z/4\) の Ext¹・Tor₁、係数写像、拡大の類 |
| `Cyclic.ProjectiveCoefficient` | \(\operatorname{Tor}_n(\mathbb Z/2,\mathbb Z)=0\)、\(n>0\) |
| `Cyclic.DoubleTensor.Balanced` / `BalancedExact` | 両側の分解比較、変数交換と接続写像 |
| `ExactSequences` | \(0\to\mathbb Z\to\mathbb Z^2\to\mathbb Z\to0\) と自然性 |
| `Finite` | 非対角の三項整数複体、基底変更、生成元と誘導写像 |
| `Finite.Bounded.UniversalCoefficient` | Ext¹・Hom / テンソル・Tor₁ の短完全列と分裂 |
| `Finite.Bounded.IntegerTor` / `IntegerTensor.Selected` | 全次数3の Tor 項 \(\mathbb Z/2\)、生成元の持ち上げと射影 |
| `Finite.Bounded.IntegerTensorNaturality` | 非自明な基底変更による短完全列の両四角形 |
| `Field.Tensor` | 標準外積、分裂変更、交換符号、左右の単位 |

```sh
cargo run -p cli -- libs/algebra/homological/concrete_complexes --module concrete_complexes --memory-mib 15872 --batch-seconds 60 --diagnostics compact
```

`--module concrete_complexes.Finite.Bounded.UniversalCoefficient` などで例を選べる。
