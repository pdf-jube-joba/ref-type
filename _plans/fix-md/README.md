# `gaps.md` と分割先の再現・原因調査

当初の調査・再検証ベースは `9c84db29074bd2712f1efa4ec18f4d2a925fb651`。
`git fetch origin` 後の `origin/main` の SHA を確認し、指定された `d56d19914e9cc9c3fa5fe1e54415ec042bd20e62` が祖先に含まれることを `git merge-base --is-ancestor` で検証した。
作業ツリーが clean な状態から `investigate/gaps-numbering-minimal` を作成した。
当初の原因調査は `d56d199…` で行っており、当時の再検証ベース `9c84db2…` との間に `src/`、`libs/`、`tests/`、Cargo manifest・lockfile の変更はなかった。
実行環境は Linux x86_64、Rust 1.95.0、Python 3.12。

## G03・G04 の実装後の再検証

2026-10-06、最新 main `6571149ca98b78191db0066b2e00b64740c797cc` から G03・G04 を修正した。
修正前の CLI でも G03.01・G03.03・G04.01・G04.03 の失敗を再確認し、修正後は対照例を含む10例が成功する。
以下の G03・G04 の記述と例の期待値は実装後の状態であり、他の項目と `evidence/` は当初の調査記録である。
後から `gaps.md` に加わった G13 は、この G01〜G12 の調査カタログには含めない。

```sh
cargo build --locked -p cli
python3 _plans/fix-md/run.py --groups G03 G04
cargo test --locked -p elaboration --test gaps_g03_g04
```

`cargo test --locked --workspace` は追加の6テストを含む328テストが成功し、`cargo fmt --all -- --check` と `git diff --check` も成功した。
`tests/bench_libraries.py --runs 1` で std・real・complex・linear_algebra・topology・calculus・integration・category の全8ライブラリを `--no-cache --diagnostics compact` で検査し、すべて終了0を確認した。
誤った証明・注釈、存在証人の集合値への脱出、部分集合への証明なしの導入、不正な constructor 引数・名前・枝、禁止された Prop 消去を拒否する回帰テストを含む。

`Logic.Proposition.andElim` の `(curried: P -> Q -> R) (value: And[P, Q])` を `(curried: _) (value: _)` に短縮した。
方向微分の部分集合型注釈を `_` にし、微分順序の `Lists.List[Coordinate]::nil` と帰納法を `Directions` 経由に変更した。
変更した5つのライブラリ `.ref` は24,055文字から23,749文字へ306文字、499行から498行へ1行減り、宣言された定理の型と証明内容を維持している。

## 対象文書の対応

G01〜G10 は現行の [`gaps.md`](../gaps.md) の掲載順と一致する。
[`box-parameters.md`](../box-parameters.md#g11) を G11、[帰納型の再帰的な述語](#g12) を G12 として続ける。
各例の ID は `G親番号.枝番`、ファイル名は `親番号-枝番-内容.ref` で、失敗例と対照例を同じ親番号にまとめる。
元文書の人間のメモは保持している。
対応データは [`catalog.json`](catalog.json) に保存する。

| ID | 元文書の項目 | 結論と失敗する段階 |
| --- | --- | --- |
| [G01](#g01) | [record eta 則](../gaps.md#g01) | 変数に対する定義的 eta はない。kernel の conversion で失敗。命題的等式は kernel の帰納法で証明できる。 |
| [G02](#g02) | [命題を条件とする集合値の構成](../gaps.md#g02) | 一級の `P -> A` は sort の積規則により拒否。contextual な `choose(h: P): A` は成功。 |
| [G03](#g03) | [宣言された型からの証明引数の推論](../gaps.md#g03) | 対応済み。宣言型を lambda・ブロック・局所定義へ渡し、現在の束縛文脈で型を単一化する。 |
| [G04](#g04) | [定義した型名からの帰納型の操作](../gaps.md#g04) | 対応済み。型の展開結果から constructor と induction の帰納型を解決する。 |
| [G05](#g05) | [モジュール引数に依存する部分集合型の商](../gaps.md#g05) | 再現。具体化時の宣言予約順と共有判定により、内側 import の古い型参照を再利用する。 |
| [G06](#g06) | [具体化したモジュール内の型と座標空間](../gaps.md#g06) | 内部の帰納型の同じ不一致を恒等関数まで縮約して再現。G05 と同じ具体化・共有経路。 |
| [G07](#g07) | [圏の signature を添字に取る Set の構造](../gaps.md#g07) | 再現。signature parameter の宣言側の展開と、利用側の実引数の展開が揃わない。 |
| [G08](#g08) | [contextual な定義をモジュール引数に渡す](../gaps.md#g08) | 再現。展開後の構文に残る穴を elaboration の import 引数検査が拒否。 |
| [G09](#g09) | [ブロックで導入した contextual な関手の射影](../gaps.md#g09) | 再現。block のローカル束縛を伴わずに射影を正規化し、名前解決で module import と解釈する。 |
| [G10](#g10) | [集合値関手の内部で具体化した自然変換の型](../gaps.md#g10) | 現行 main では再現せず。自己完結した2例と実ライブラリの一時コピーによる確認が成功。解消コミットは未特定。 |
| [G11](#g11) | [Machine の実行を Box にする定義](../box-parameters.md#g11) | 再現。kernel が開いた computation type を拒否する、現行仕様の閉性制限。 |
| [G12](#g12) | [帰納型の再帰的な述語](README.md#g12) | 修正済み。`induction` が開いた motive を直接検査し、命題・述語への再帰が成功。 |

## 単独ファイルとしての実行条件

`cases/` の各 `.ref` は、それぞれ必要な定義とトップレベルの `\module` を含む。
他の `.ref`、`ref.toml`、標準ライブラリ、外部パッケージを必要としない。
同一ファイル内の `\root.Repro[]` などの参照は、外部ファイルの import ではない。
CLI の `.ref` 入力はトップレベルに module を要求するので、元文書の式や宣言を module に収めている。

リポジトリのルートで実行する。

```sh
cargo build --locked -p cli
python3 _plans/fix-md/run.py
```

`run.py` は全39ファイルを**1つずつ別の空の一時ディレクトリへコピー**し、そのディレクトリを cwd として `--parse-only` と通常の検査を実行する。
両方で `--no-cache --diagnostics compact` を指定し、診断に影響する `REF_TYPE_*`、調査用の環境変数、`RUST_LOG` を除去する。
各実行には30秒の上限がある。
実行前に `gaps.md` の掲載順・番号・題名、分割先の番号・題名、対応表、説明中の枝番とファイル名、全ファイルの一対一対応、物理行数を検査する。
登録外・欠落・重複した例、飛び番、30行超過を検出すると終了1にする。
`--validate-only` で番号と行数だけを検査でき、出力 JSON には各例の ID・行数・SHA-256 と実行結果を保存する。
失敗例は、既存の `tests/ng` と同じ `/* expect-error: ... */` 形式で診断を宣言する。
終了コード1と診断の一致を確認し、panic・timeout は成功として扱わない。
全例は parse に成功し、通常検査は17件が想定した診断で終了、22件が成功した。
39例すべてが空行・コメント込み30行以内で、最大は G10.01 の30行である。

個々のコマンドは次の形になる。
以下の一覧の任意のファイル名で置き換えられる。

```sh
target/debug/cli _plans/fix-md/cases/05-01-dependent-type-minimal.ref --no-cache --diagnostics compact
target/debug/cli _plans/fix-md/cases/05-01-dependent-type-minimal.ref --no-cache --parse-only
```

全件の終了コード・標準出力・標準エラーは [`evidence/results.json`](evidence/results.json) に保存した。
ログ中の `<isolated>` は、一時ディレクトリのパスを正規化したもの。
再取得は次のコマンドで行える。

```sh
python3 _plans/fix-md/run.py --validate-only
python3 _plans/fix-md/run.py --output /tmp/ref-results.json
```

`src/cli/tests/ref_files.rs` が自動収集するのは `tests/ok` と `tests/ng`。
この調査資料は `_plans/fix-md/` に置き、現行の失敗を固定するケースは通常のテスト集合に追加していない。

<a id="g01"></a>

## G01: record eta

- **G01.01** [`01-01-record-eta.ref`](cases/01-01-record-eta.ref): `s = Record { field := s.field }` を `refl(s)` で示したい。終了1、`types are not convertible`。
- **G01.02** [`01-02-record-eta-concrete.ref`](cases/01-02-record-eta-concrete.ref): `s` を具体的な constructor 値にした対照例。終了0。

sort を持つ structure は単一 constructor の帰納型へ展開される（[言語仕様](../../doc/book/src/language/structure.md#sort-を持つ-record)）。
[`reduction::convertible`](../../src/kernel/src/reduction.rs#L609) は beta・弱頭簡約と構文の比較を行い、変数と constructor による再構成を一致させる record eta 規則を持たない。
変数の射影は簡約しないため、左の変数と右の constructor 適用が異なるまま残る。
具体的な record では射影が簡約し、対照例が成功する。

これは「この等式が体系で証明不可能」という結論ではない。
[`kernel_probe.rs`](kernel_probe.rs) は同じ単一 constructor の型で、`refl` の拒否と直接の `IndElim` による eta 等式の証明成功を確認する。
この kernel API の成功と、表面構文から record の帰納法を利用できるかは別問題である。

<a id="g02"></a>

## G02: 証明から集合値へ

- **G02.01** [`02-01-proof-function.ref`](cases/02-01-proof-function.ref): 一級の関数型 `P -> A`。終了1、`no product rule for these sorts`。
- **G02.02** [`02-02-proof-contextual.ref`](cases/02-02-proof-contextual.ref): `choose(h: P): A := a` とその適用・計算の等式。終了0。

[`Sort::product`](../../src/kernel/src/sort.rs#L65) は domain が `Base(Prop)`、body が `Base(Set)` の組を許していない。
したがって通常の lambda と product による関数化は仕様上の制限である。
一方、[`elaborate_contextual_definition`](../../src/elaboration/src/elaborator/declarations.rs#L5) は引数を文脈として保持し、その文脈で結果と本体を検査する。
全引数を一つの kernel product に包まないため、contextual 定義は成功する。
「証明を引数にするすべての集合値の定義が不可能」とする説明は広すぎる。
この対照例は Urysohn 関数の構成全体を証明するものではなく、問題となる引数・結果の分類を確認する。

<a id="g03"></a>

## G03: 宣言型からの推論

| 例 | 期待・確認対象 | 実測 |
| --- | --- | --- |
| **G03.01** [`03-01-infer-projection.ref`](cases/03-01-infer-projection.ref) | 元文書の `andElim`。`value: _` を宣言型から決める。 | 終了0。 |
| **G03.02** [`03-02-explicit-projection.ref`](cases/03-02-explicit-projection.ref) | `value: And[P,Q]` のみ明示。 | 終了0。 |
| **G03.03** [`03-03-infer-take-continuation.ref`](cases/03-03-infer-take-continuation.ref) | `exists A -> (A -> P) -> P` の存在消去で `step: _` を推論する。 | 終了0。 |
| **G03.04** [`03-04-explicit-take-continuation.ref`](cases/03-04-explicit-take-continuation.ref) | `step: A -> P` のみ明示。存在証明 `e` は `_` のまま。 | 終了0。 |
| **G03.05** [`03-05-infer-take.ref`](cases/03-05-infer-take.ref) | 証人を関数へ渡さず、既知の証明を返す存在消去。`e: _`。 | 終了0。 |
| **G03.06** [`03-06-infer-subset.ref`](cases/03-06-infer-subset.ref) | 部分集合型の引数を `f: A -> A` に渡した後にも `bysub` で所属を取り出す。 | 終了0。 |

定義本体を宣言型の期待値付きで elaboration し、lambda の注釈を本体の射影や存在消去より先に単一化する。
同じ期待型を複数変数の束縛、ブロック、型注釈付き局所定義、structure の検査用ラッパーへ伝える。
単一化は module 引数と現在のローカル束縛を含む文脈で行い、依存型や部分集合型を保持する。
完成した定義は従来どおり kernel で再検査する。
期待型なしの未知の関数適用を一般に推論できるようにする変更ではなく、当初の `kernel_probe.rs` にある独立した未知関数型の制限とは区別する。

<a id="g04"></a>

## G04: 定義名を経由する帰納型の操作

- **G04.01** [`04-01-alias-constructor.ref`](cases/04-01-alias-constructor.ref): `Directions := List[Coordinate]` の後の `Directions::nil`。終了0。
- **G04.02** [`04-02-direct-constructor.ref`](cases/04-02-direct-constructor.ref): constructor の参照を `List[Coordinate]::nil` に戻す。終了0。
- **G04.03** [`04-03-alias-induction.ref`](cases/04-03-alias-induction.ref): `induction (xs: Directions)`。終了0。
- **G04.04** [`04-04-direct-induction.ref`](cases/04-04-direct-induction.ref): 帰納法の型を `List[Coordinate]` に戻す。終了0。

関連名のアクセスは型を検査してから正規化し、展開結果の帰納型と実引数から constructor を構成する。
帰納法は motive の telescope を elaboration した後に末尾の型を正規化するため、添字付きの別名も扱える。
複数段の定義、contextual な型定義、具体化した module の型名に対応する。
部分集合型の台集合を帰納型として取り出すことはせず、constructor の引数、帰納法の枝・motive、Prop の消去制限は元の kernel で検査する。
追加回帰テストは [`gaps_g03_g04.rs`](../../src/elaboration/tests/gaps_g03_g04.rs) を参照。

<a id="g05"></a>

<a id="g06"></a>

## G05・G06: 外側の具体化後に残る内側 import の型

| 例 | 確認する形 | 実測 |
| --- | --- | --- |
| **G05.01** [`05-01-dependent-type-minimal.ref`](cases/05-01-dependent-type-minimal.ref) | 商を除去し、`Pass[A]` の恒等関数と依存する部分集合型だけにする。 | 終了1。 |
| **G05.02** [`05-02-independent-type.ref`](cases/05-02-independent-type.ref) | predicate の `x = u` を `x = x` にする。 | 終了0。 |
| **G05.03** [`05-03-dependent-quotient.ref`](cases/05-03-dependent-quotient.ref) | 代表元・同値類・Carrier を同じファイルで定義し、`interval` に依存する集合を商へ渡す。 | 終了1。 |
| **G05.04** [`05-04-concrete-quotient.ref`](cases/05-04-concrete-quotient.ref) | 具体的なスコープで商を import する。 | 終了0。 |
| **G06.01** [`06-01-inner-inductive-minimal.ref`](cases/06-01-inner-inductive-minimal.ref) | parameter を持つモジュール内の `Unit` を `Pass[A]` に渡し、外側を具体化する。 | 終了1。 |
| **G06.02** [`06-02-outer-inductive.ref`](cases/06-02-outer-inductive.ref) | `Unit` を外側で宣言する。 | 終了0。 |
| **G06.03** [`06-03-inner-inductive.ref`](cases/06-03-inner-inductive.ref) | 縮約途中の座標関数と法則だけの例。 | 終了0。この弱い例だけでは報告の失敗を検出できない。 |

期待するのは、外側のモジュールの具体化が、そこに保持された内側の import と型にも伝わることである。
実際の G05 の診断は、具体化済みの `Outer[u := Unit::unit].Representation` と元の `Outer.Representation(u)` の不一致。
G06 は `Outer[K := Scalar].Unit` と元の `Outer.Unit` の不一致となる。
どちらも `definition body check failed: types are not convertible` である。
G06 は元の体・基底・trace 全体の再実装ではなく、報告にある内部の型 identity の衝突を直接検出する縮約例である。

原因の経路を調査用ログでも確認した。

1. [`module_manager`](../../src/elaboration/src/elaborator/module_manager.rs#L551) は、外側モジュールの既存 `bindings()`、すなわち内側 import の具体化済み宣言を、外側自身の宣言より先に `materialization_sources` に積む。
2. [`reserve_lazy_definition`](../../src/elaboration/src/raw/environment.rs#L801) は、その時点の remapping を使って名前空間の引数を変換し、既存の具体化を共有できるか判定する。
3. 内側 `Pass.identity` の予約時点では、外側の `Representation` または `Unit` の新しい ID がまだ remapping にない。
   名前空間引数は古い型のままで、以前の `Pass.identity` と同じ引数だと判定される。
4. ログでは内側の定義が `DefId { module: ModuleId(6), index: 0 }` → **同じ ID** に対応する。
   その後、外側の `Representation` / `Unit` は `ModuleId(3)` → `ModuleId(10)` に具体化される。
5. 完成した remapping は新規予約された宣言だけへ設定される（[`set_lazy_definition_remapping`](../../src/elaboration/src/elaborator/module_manager.rs#L762)）。
   共有された内側の古い定義はそのまま残り、外側の恒等関数の binder は新しい型、body の呼出先は古い型となる。
6. [`resolve_definition` → `check_definition`](../../src/elaboration/src/raw/environment.rs#L612) の遅延生成時の再検査で kernel が不一致を拒否する。

[`05-materialize.log`](evidence/05-materialize.log) と [`06-materialize.log`](evidence/06-materialize.log) に、予約時の不完全な対応表、最終対応表、生成された binder・body を記録した。
この2例では、parser・名前解決・型理論上の制限ではなく、elaboration の具体化と共有の順序が原因である。
kernel が異なる型のまま渡された引数を拒否すること自体は正しい。

ログ用の変更は [`materialize-trace.patch`](evidence/materialize-trace.patch) に保存した。
これは環境変数で有効になる出力の追加だけであり、チェックアウトの Rust ソースには適用していない。
再測定する場合は作業用コピーで次を実行する。

```sh
git apply _plans/fix-md/evidence/materialize-trace.patch
cargo build --locked -p cli
REF_INVESTIGATION_TRACE=1 target/debug/cli _plans/fix-md/cases/05-01-dependent-type-minimal.ref --no-cache --diagnostics compact
REF_INVESTIGATION_TRACE=1 target/debug/cli _plans/fix-md/cases/06-01-inner-inductive-minimal.ref --no-cache --diagnostics compact
git apply -R _plans/fix-md/evidence/materialize-trace.patch
cargo build --locked -p cli
```

<a id="g07"></a>

## G07: signature を sorted structure の添字にする

- **G07.01** [`07-01-signature-index-minimal.ref`](cases/07-01-signature-index-minimal.ref): `Carrier { A: Set }` と `Holder[C: Carrier] { value: C.A }` まで縮約。同じ失敗。
- **G07.02** [`07-02-flattened-argument.ref`](cases/07-02-flattened-argument.ref): 同じ `Holder` 宣言の利用側だけを `Holder[C.A]` にする。終了0。
- **G07.03** [`07-03-signature-index.ref`](cases/07-03-signature-index.ref): 元の `Functor[C,D]` と `identity`。終了1、`Failed to access item at path ... C`。
- **G07.04** [`07-04-explicit-index.ref`](cases/07-04-explicit-index.ref): 元文書の回避策どおり Set と Hom を明示した添字にし、contextual な `Functor C D` でまとめる。終了0。

sorted structure の宣言側は [`Resolver::item`](../../src/resolve/src/resolver.rs#L485) から [`expand_structure_parameters`](../../src/resolve/src/structures/parameters.rs#L194) を通る。
`C: Carrier` は `C.A: Set` へ展開され、`C` 自体は kernel の一つの値にはならない。
一方 `Holder[C]` の実引数は、同じ signature の field 群へ展開されず、裸の `C` を式として elaboration する。
[`get_item_from_access_path`](../../src/elaboration/src/elaborator.rs#L241) が、通常の item として存在しない `C` を取得できずに失敗する。
`Holder[C.A]` が成功することも、この宣言側と利用側の非対称性を確認する対照である。

今回の例では `Holder` / `Functor` の宣言自体は成功し、利用時に失敗した。
これを「signature を展開した全ての添字が sort 規則上禁止されている」と説明することはできない。
元文書の別の形で発生したという sort 診断は、今回の同じ例からは観測していない。

<a id="g08"></a>

## G08: contextual な定義を import 引数にする

- **G08.01** [`08-01-contextual-argument.ref`](cases/08-01-contextual-argument.ref): signature を引数にする `identity` の lambda 注釈を `_` とし、`K := identity C` を渡す。終了1、`module arguments do not allow inference holes`。
- **G08.02** [`08-02-explicit-argument.ref`](cases/08-02-explicit-argument.ref): lambda 注釈だけを明示。終了0。
- **G08.03** [`08-03-bound-argument.ref`](cases/08-03-bound-argument.ref): `_` を持つ元の定義を通常の定義 `bound` として先に検査してから渡す。終了0。

signature を取る front definition は、[`normalize_structures`](../../src/resolve/src/structures/normalization.rs) で本体と適合検査を含む `Checked` 式へ展開される。
テンプレートにあった `_` もその構文に残る。
[`require_explicit_module_argument`](../../src/elaboration/src/elaborator/modules.rs#L22) は、型推論を始める前に構文を走査し、`SExp::Meta` があれば拒否する。
従って、`identity` の宣言時の型検査が成功していても、展開されたソースの穴は module 引数の制限に引っかかる。
これは kernel の型不一致ではなく、elaboration の明示的な穴禁止と front definition の展開との組み合わせである。

<a id="g09"></a>

## G09: block 内の射影

- **G09.01** [`09-01-block-minimal.ref`](cases/09-01-block-minimal.ref): contextual 関手を除き、普通の `Box[A]` の `x.field` だけにする。終了1、`Module import 'x' was not found`。
- **G09.02** [`09-02-block-hash-projection.ref`](cases/09-02-block-hash-projection.ref): `x.field` を `x #field` にする。終了0。
- **G09.03** [`09-03-block-projection.ref`](cases/09-03-block-projection.ref): 元の関手の `component`。終了1、`Module import 'F' was not found`。
- **G09.04** [`09-04-lambda-outside.ref`](cases/09-04-lambda-outside.ref): `F,G,H` の lambda だけを block の外へ移す。終了0。

[`Resolver::expression`](../../src/resolve/src/resolver.rs#L246) は structure の正規化 → lexical binding の処理 →参照解決の順に進む。
[`normalize_structures`](../../src/resolve/src/structures/normalization.rs#L15) は `TakeFrom` を含む block を早期に通常の項へ展開するが、今回の `Fun`・`Let` だけの block はその分岐に入らない。
通常の lambda にはローカルスコープを延長する処理がある一方、block の `Statement::Fun` をその段階の `locals` に加える処理はない。
そのため `x.field` / `F.object` がローカル値の射影へ書き換わらず、`LocalAccess::Named` のまま残る。
[`Resolver::access`](../../src/resolve/src/resolver.rs#L289) がこれを import alias として探し、名前解決エラーにする。
parser は全例を受理しており、kernel の射影や contextual 関手固有の制限ではない。

<a id="g10"></a>

## G10: 自然変換の型の内部 import

- **G10.01** [`10-01-nested-transformation.ref`](cases/10-01-nested-transformation.ref): signature、`hom`、refinement による自然変換の型、内部 import、具体化後の `evaluate`。30行、終了0。
  `HomCarrier` の補助定義を除き、`hom` の `Carrier` に本体を直接書いた。
  この例の条件は自己等式に縮約しているため、自然性の完全な検証とは区別する。
- **G10.02** [`10-02-yoneda-endomorphisms.ref`](cases/10-02-yoneda-endomorphisms.ref): 自己関数を射とする圏の表現可能関手に限定し、実際の自然性と `evaluateFromElement` を検査する。28行、終了0。
  `Hom(v,w) := C.Object -> C.Object`、恒等射は恒等関数、合成は関数合成として、汎用の圏・関手のデータと法則の record を除去した。
  `fromElement p` は `f` を `f ∘ p` に送る族で、自然性は合成の結合性から `refl`、評価後の等式は関数外延性から証明する。
  `Transformations` の refinement を別の内部 import `Yoneda.Maps` の引数型として使用し、`C.Object := Unit` への具体化後に往復の等式を検査する。
  以前の114行の例が扱っていた一般の `Diagram P` と全法則は、この縮約例の範囲外である。

さらに [`yoneda_library_probe.py`](yoneda_library_probe.py) は、実際の `libs/category` と `tests/projects/category` を一時ディレクトリへコピーする。
`SetValued.On.Yoneda` のローカルな自然変換型の構成を、元文書にある `Transformations[P := hom u, Q := P]` の内部 import に置き換え、実際の利用例全体を `--no-cache` で検査する。
これも終了0で、診断はなかった。
この補助実験は package の `ref.toml` と現行の `libs/std` が必要であり、**完全な単独ファイル**ではない。
単独ファイルの検査は上の2例で別途行っている。

```sh
python3 _plans/fix-md/yoneda_library_probe.py
```

以上の条件では、元文書の `Unit` と `C.Object` の不一致は再現しなかった。
現行の具体化・型検査を成功したという観測であり、過去の失敗を起こした完全な入力や解消したコミットを同定したものではない。
G05・G06 と似た診断だったことだけを理由に、同じ原因だったとは断定しない。

<a id="g11"></a>

## G11: Machine の Box

- **G11.01** [`11-01-box-machine.ref`](cases/11-01-box-machine.ref): signature の `State`・`Output`・`run` だけを残した `runBox(machine)`。終了1、`Box requires a closed computation type`。
- **G11.02** [`11-02-box-concrete.ref`](cases/11-02-box-concrete.ref): 閉じた `Unit` の Machine を先に構成して Box にする。終了0。

signature は依存する field の文脈へ展開される。
この時点の `machine.State ~> F(machine.Output)` は開いた型である。
[`Checker::closed_program_type`](../../src/kernel/src/check.rs#L1435) は自由な束縛変数または module parameter を検出して拒否する。
payload の型検査や reflection を通す前に、この computation type の検査で失敗する。
[Box の規則](../../doc/book/src/system.md#boxed-computation-2) は computation type と payload を空文脈で型検査するため、現行仕様に沿った拒否である。
型の穴 `_` を明示型にするだけでは閉性は変わらない。

<a id="g12"></a>

## G12: 帰納型の再帰的な述語

修正前は `prec` と `induction` が motive の通常のラムダを先に推論し、`upper sort has no classifier` で失敗した。
修正後は kernel の `IndElim` に telescope と本体を渡し、次の三例が成功する。

- **G12.01** [`12-01-predicate-family.ref`](cases/12-01-predicate-family.ref): `return Nat -> Prop` による述語の再帰。
- **G12.02** [`12-02-predicate-induction.ref`](cases/12-02-predicate-induction.ref): `return Prop` による命題の再帰。
- **G12.03** [`12-03-predicate-powerset.ref`](cases/12-03-predicate-powerset.ref): `Pow Nat` への再帰と所属命題。

通常の motive ラムダの拒否と、開いた motive による消去・簡約の成功は `kernel_probe.rs` で確認する。
元の実数上の二項述語 `Valid` も `libs/integration/src/Real/Division.ref` で直接の `induction` に変更した。

## Kernel の独立確認と全体検証

```sh
python3 _plans/fix-md/kernel_probe.py
```

この補助コマンドは現行の kernel をビルドし、`kernel_probe.rs` を一時ディレクトリにコンパイルして実行する。
workspace の crate にテストや機能を追加せず、G01・G03・G12 の境界を kernel API で直接確認する。
結果は [`kernel-probe.txt`](evidence/kernel-probe.txt)。

最終状態の再現例を空のディレクトリで全件再実行し、調査用ログの追加を取り除いたソースから作った CLI で検証した。
`cargo test --locked --workspace` で通常の fixture と、`tests/projects/library`・`tests/projects/category` を含む既存テストを検査した。
番号検査は正常な資料に加え、31行、見出し順の不一致、枝番の不一致、説明の ID の不一致、登録外ファイル、欠落ファイルを一時コピーに作って確認した。
全7条件の結果は [`catalog-negative-checks.json`](evidence/catalog-negative-checks.json) に記録する。
`cargo test --locked --workspace` の検査結果と環境情報は [`validation.json`](evidence/validation.json) に記録する。

```sh
cargo build --locked -p cli
python3 _plans/fix-md/run.py
python3 _plans/fix-md/kernel_probe.py
python3 _plans/fix-md/yoneda_library_probe.py
cargo test --locked --workspace
```
