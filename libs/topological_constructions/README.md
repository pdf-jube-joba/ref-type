# 位相空間の構成

積、商、直和、貼り合わせ、compact-open 位相を扱う。
公開 module は [root.ref](src/root.ref)、直接依存は [ref.toml](ref.toml) にある。

| module | 公開する内容 |
| --- | --- |
| `topological_constructions.Product.Compactness` | 開集合の局所的な開矩形による表示、tube lemma、コンパクト集合の二因子積。 |
| `topological_constructions.Product.Maps` / `Continuity.Corestriction` | 積の射影と部分空間への値域制限の連続性。 |
| `topological_constructions.RelationQuotient` | 同値類の集合に商位相を与え、関係を保つ写像を一意に降ろす構成と連続性。 |
| `topological_constructions.Coproduct` / `topological_constructions.Pushout` | 位相的直和、写像に沿う貼り合わせ、互換な連続写像の降下。 |
| `topological_constructions.Quotient` | 写像の終位相、商写像、商からの写像の連続性の普遍性。 |
| `topological_constructions.Gluing` | 開被覆と有限閉被覆による連続性の貼り合わせ、部分空間への制限からの局所条件の導出。 |
| `topological_constructions.Gluing.BinaryClosed` / `topological_constructions.Gluing.Pasting` | 二つの閉集合の被覆上での連続性判定と一致する写像の貼り合わせ。 |
| `topological_constructions.ProductQuotient` | コンパクト Hausdorff 因子と商写像の積が商写像となる定理。 |
| `topological_constructions.FunctionSpace.Of` | 連続写像の集合上の compact-open 位相と、連続写像との前合成の連続性。 |

検査方法と関連パッケージは [ライブラリ一覧](../README.md) を参照。
