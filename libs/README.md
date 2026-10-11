# ライブラリ

各パッケージの `ref.toml` が依存先、`src/root.ref` が公開 module を定める。
`std` 以外は約5,000行を目安に、共有する基礎から応用へ依存する単位に分ける。
行数は `src/**/*.ref` の合計である。

| パッケージ | 内容 | 行数 | 直接依存 |
| --- | --- | ---: | --- |
| [std](std/README.md) | 論理、データ、整数・有理数、商、代数構造 | 18,612 | なし |
| [algebra](algebra/README.md) | 準同型、群完成、商、多項式環 | 1,545 | std |
| [module_theory](module_theory/README.md) | 環上の加群、自由加群、直和、テンソル積、完全列 | 5,322 | algebra, std |
| [commutative_algebra](commutative_algebra/README.md) | Hom とテンソル積、射影性、有限自由加群の行列 | 1,295 | algebra, module_theory, std |
| [integer_matrices](integer_matrices/README.md) | 整数行列の演算、Smith 標準形と変換行列 | 4,976 | algebra, commutative_algebra, module_theory, std |
| [finitely_generated_modules](finitely_generated_modules/README.md) | 整数の核・像・部分加群の基底、巡回加群、体上の有限次元部分空間 | 1,664 | algebra, commutative_algebra, integer_matrices, module_theory, std |
| [ordered_fields](ordered_fields/README.md) | 順序体と上限完備性の共通構造 | 131 | std |
| [dedekind_reals](dedekind_reals/README.md) | 有理数の切断による実数、演算・順序・完備性 | 4,593 | ordered_fields, std |
| [cauchy_reals](cauchy_reals/README.md) | 有理数 Cauchy 列の商による実数、演算・順序・完備性 | 3,886 | ordered_fields, std |
| [real](real/README.md) | 構成済みの実数の演算、距離評価、数列、平方根、有限和 | 1,785 | dedekind_reals, std |
| [chain_complexes](chain_complexes/README.md) | 自然数・整数次数の複体、ホモロジー、写像・ホモトピー・複体の圏 | 4,966 | algebra, category, module_theory, std |
| [resolutions](resolutions/README.md) | 非負鎖複体、射影分解、比較定理、Hom・テンソル複体、二重複体 | 4,769 | algebra, chain_complexes, commutative_algebra, module_theory, std |
| [derived_functors](derived_functors/README.md) | Ext・Tor、分解からの独立性と自然性、巡回加群の分解、普遍係数 | 3,352 | algebra, chain_complexes, commutative_algebra, finitely_generated_modules, module_theory, resolutions, std |
| [homological_algebra](homological_algebra/README.md) | 有限複体のホモロジー計算、テンソル余鎖複体、Künneth 同型 | 5,363 | algebra, chain_complexes, commutative_algebra, derived_functors, finitely_generated_modules, integer_matrices, module_theory, resolutions, std |
| [linear_algebra](linear_algebra/README.md) | 体上の線形代数、多重線形・外代数、実数・複素数への具体化 | 5,175 | algebra, complex, dedekind_reals, module_theory, real, std |
| [complex](complex/README.md) | 実数対による複素数と体の構造 | 432 | dedekind_reals, real, std |
| [category](category/README.md) | 圏、関手、自然変換、普遍性、随伴、加法圏・アーベル圏 | 1,767 | std |
| [calculus](calculus/README.md) | 極限、平均値定理、多変数微分、滑らかな写像 | 5,210 | dedekind_reals, linear_algebra, metric_spaces, real, std, topological_algebra, topology |
| [integration](integration/README.md) | リーマン積分、L¹ 完備化によるルベーグ積分 | 556 | dedekind_reals, real, std |
| [manifolds](manifolds/README.md) | アトラス、滑らかな写像、接空間と微分 | 2,452 | calculus, linear_algebra, real, std, topological_algebra, topology |
| [algebraic_topology](algebraic_topology/README.md) | ホモトピー、基点付き商、mapping cone、有限 CW 対 | 1,382 | dedekind_reals, metric_spaces, real, std, topological_algebra, topological_constructions, topology |
| [topological_algebra](topological_algebra/README.md) | 位相的代数、座標空間・行列位相、連続性判定 | 1,013 | complex, dedekind_reals, linear_algebra, metric_spaces, real, std, topological_constructions, topology |
| [topology](topology/README.md) | 位相・部分空間、連続写像、コンパクト性、分離性 | 4,632 | dedekind_reals, std |
| [metric_spaces](metric_spaces/README.md) | 距離位相、距離化、実数直線、実数値関数、有限従属分割 | 2,401 | dedekind_reals, real, std, topology |
| [topological_constructions](topological_constructions/README.md) | 積、商、直和、貼り合わせ、compact-open 位相 | 1,450 | std, topology |
| [euclidean_forms](euclidean_forms/README.md) | 局所微分形式、外積・外微分、座標表示、引き戻し | 2,576 | calculus, chain_complexes, linear_algebra, module_theory, real, std |
| [differential_forms](differential_forms/README.md) | 大域微分形式、貼り合わせ、引き戻し、De Rham コホモロジー | 2,947 | calculus, chain_complexes, euclidean_forms, linear_algebra, manifolds, module_theory, real, std, topology |

加群の共通構造は `module_theory`、可換環上の Hom・テンソルと行列は `commutative_algebra` に置く。
`chain_complexes` は De Rham 複体とホモロジー代数の両方が利用し、`euclidean_forms` は多様体上の形式から独立して局所計算を提供する。
`ordered_fields` の共通構造を二つの実数構成が実装し、解析で使う標準の実数は `dedekind_reals` から `real` に渡す。

共通の数値的な補題は `real.Analysis` に置き、微分・積分・位相・線形代数が利用する。
`Def` / `Prop` は演算と法則を分けた module、単独の関心ごとは `Distance` / `Sequence` などの名前で公開する。
証明の等式連鎖には [eq_reason!](std/README.md#等式と合同則) を使える。

## 型検査

リポジトリのルートで実行する。

```sh
cargo run -p cli -- --full-check libs
```

`libs/ref.toml` は全ライブラリを依存先に持つ検査用パッケージである。
Linux の CLI は、一つの検査プロセスの仮想メモリを3072 MiBに制限する。
メモリ上限に達した範囲や180秒を超えた大きな範囲は、親 module 自身の宣言と各子 module に分割し、それぞれの参照先を含めて別プロセスで検査する。
これ以上分割できない範囲は時間で打ち切らず、メモリ上限内で検査を続ける。
同時に動かす検査プロセスは一つで、プロセス終了時に環境全体のメモリを解放する。
進捗表示と中断は親プロセスが管理し、Ctrl+Cで実行中の子プロセスも停止する。

通常の実行では入力先の `refcache/` にある検査結果を再利用する。
`--full-check` は実行ごとに空の検査キャッシュから始め、同じ実行中に確認できた結果を共有し、完了後に通常のキャッシュへ保存する。
前回分割した範囲もキャッシュに記録するため、再実行すると分割した検査から始める。
型エラー、分割できない範囲での資源不足、検査中のソース変更がある場合は失敗終了する。

```sh
cargo run -p cli -- --full-check libs/homological_algebra
cargo run -p cli -- libs
cargo run -p cli -- tests/projects/manifolds-de-rham
```

[library project](../tests/projects/library/src/root.ref) は分野間の接続と具体例、[category project](../tests/projects/category/src/root.ref) は圏論の利用例を検査する。
処理系のテストとキャッシュの指定は [利用方法](../src/USAGE.md) を参照。

[位相的 K 理論の基礎 project](../tests/projects/topological-k-theory/src/root.ref) は群完成、直和、行列位相、ホモトピー、商、セル付着を接続する。
