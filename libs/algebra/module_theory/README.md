# 加群論

環上の加群、自由加群、直和、テンソル積、完全列を扱う。

| module | 公開する内容 |
| --- | --- |
| `module_theory.Module.Over` | 台集合と加群構造の束、準同型の可換加法群、部分加群・核・像・商。 |
| `module_theory.Module.Over.FirstIsomorphism` | 核による商と像との同型。 |
| `module_theory.Module.Over.Presentation` / `Free` | 形式和と関係による加群、生成元による準同型の一意な延長、自由加群の射影性。 |
| `module_theory.Module.Over.Free.Reindex.Injection.Retraction` | 生成元の単射に沿う自由加群の包含の左逆。 |
| `module_theory.Module.Over.Free.Coefficients` / `Finite` | 係数写像、有限生成元による展開、有限支持関数との同型。 |
| `module_theory.Module.Over.Free.Induction` / `Subset` | 加群演算による帰納法、生成元の部分集合が張る部分加群と線形写像による像の判定。 |
| `module_theory.Module.Over.FiniteCoordinates` | 有限座標加群、標準基底による展開、有限集合上の自由加群との同型、先頭座標と残りの座標の分解、零拡張と先頭が零の部分加群との同型。 |
| `module_theory.Module.Over.KernelTransport` | 可換な基底変更に沿う核と余核の同型、商の類での写像の計算。 |
| `module_theory.Module.Over.Alternating` | 有限交代和、準同型との可換性、面の恒等式に対応する二重交代和の打ち消し。 |
| `module_theory.Module.Over.Product` / `DirectSum` | 任意添字の積・直和、有限支持族との同型、成分の包含、直和からの準同型の普遍性と射影性、生成元と加群演算による `Generated.induction`。 |
| `module_theory.Module.Over.FinitelySupported` | 任意加群族の積における有限支持部分加群。 |
| `module_theory.Module.Over.Biproduct` | 二項直和と積、射影・包含、組と余組の普遍性。 |
| `module_theory.Module.Over.ShortExact` / `ShortExactComparison` | 短完全列、分裂から得られる直和同型、可換図式の比較。 |
| `module_theory.Module.Over.ExactFiveComparison` | 五項完全列の可換図式における中央写像の単射・全射と同型。 |
| `module_theory.Module.Over.Pushout.On` | 二つの準同型の押し出しと、可換な写像からの一意な準同型。 |
| `module_theory.Module.Over.ShortExact.Pushout.On` | 短完全列を左端の係数写像に沿って押し出した短完全列。 |
| `module_theory.Module.Over.CanonicalFree` / `FreeResolution` | 元の集合上の自由加群からの全射、反復する核、射影的な各項と隣接する微分の完全性。 |
