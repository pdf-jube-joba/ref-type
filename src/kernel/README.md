# PTS kernel

sort・型・項・証明を共通の `kernel::syntax` の `Expression` と `Node` で表す。
`Expression` は `Arena` 内の intern 済み handle であり、子の項と binder の型も同じ arena を使う。

| モジュール | 担当 |
| --- | --- |
| [check](src/check.rs) | 型判断 |
| [sort](src/sort.rs) | sort の公理と product 関係 |
| [calculus](src/calculus.rs) | 束縛、shift、代入 |
| [reduction](src/reduction.rs) | 簡約・評価・conversion |
| [reflection](src/reflection.rs) | Program の反映 |
| [metavariables](src/metavariables.rs) | 単一化と保留制約 |
| [environment](src/environment.rs) | 宣言登録と検証済み環境 |
| [exports](src/exports.rs) | package が所有する宣言と共有式の再配置 |

`Context` は `Binding { var, ty }` を外側から並べた telescope で、各型は先行する文脈で解釈する。
`Bound(0)` は最も内側の変数、`SymbolId` は表示名であり、alpha 等価性は名前に依存しない。

## 型推論と登録

```rust
use kernel::{check::Checker, environment::{Definition, Environment},
    ids::SymbolId, metavariables::MetaContext,
    sort::{BaseSort, Sort}, syntax::{Mode, Node}};

let mut env = Environment::new();
let arena = env.arena().clone();
let set = arena.sort(Sort::Base(BaseSort::Set(0)));
let identity = arena.alloc(Node::Lambda {
    mode: Mode::Pure,
    var: SymbolId::ANONYMOUS,
    domain: set,
    body: arena.bound(0),
});
let mut metas = MetaContext::new();
let ty = Checker::new(&env, &mut metas, vec![]).infer(identity)?;
let id = env.register_definition(&mut metas, Definition {
    context: vec![], ty, body: identity,
})?;
let reference = env.reference(id, vec![])?;
assert_eq!(Checker::new(&env, &mut metas, vec![]).infer(reference)?, ty);
# Ok::<(), Box<dyn std::error::Error>>(())
```

公開 `infer` / `check` は文脈の形成を確認し、未解決メタ変数があれば `Error::Unresolved` を返す。
`register_definition` は `finish` と厳密な型検査後に `DefinitionId` を返す。
定義参照は宣言型と本体に文脈引数を同時代入し、Program 定義は反映先も検査して登録する。
module 名や source location は elaboration が保持する。

`register_inductive` は arity・constructor の戻り先・sort・strict positivity を検査する。
`register_datatype` は Program の field と parameter を検査し、Set の鏡像を登録する。
`IndElim` は motive の telescope と本体を別に保持し、添字・要素・再帰仮定を代入して各枝を検査する。
消去先の制限と singleton elimination は [check.rs](src/check.rs) を参照。

`IdElim` は命題値の等式除去と集合値の移送を表し、`family` の sort に応じて結果を検査する。
集合値の移送は neutral な head を保ち、`TransportEq` が自己移送と元との命題上の等式を証明する。
等式の certificate は型検査と通常の構造走査に含め、conversion と unification の比較対象からは消去する。

## Refinement とメタ変数

`SubsetIntro` は要素と所属証拠を検査し、refinement 型 `TypeLift` を返す。
台集合へ弱めても所属証拠を保持する。
`Environment::erased_head` は値の観測時に導入を透過し、conversion・適用・所属・消去が同じ値の見方を使う。

メタ変数は宣言文脈と期待型を持ち、出現ごとの引数列が宣言文脈からの代入を表す。

| 操作 | 役割 |
| --- | --- |
| `fresh` / `restrict` | 穴を作成 / 文脈を共通の接頭辞へ制限 |
| `infer` / `check` / `unify` | 制約生成・単一化 |
| `solve_pending` / `finish` | 保留判断の再実行 / 全検査義務の完了確認 |
| `zonk` | 解決済みメタ変数の代入 |
| `snapshot` / `rollback` | 試行前の状態を保存・復元 |

occurs check は候補・期待型・宣言文脈を通じた循環も検出する。
`finish` は結果から到達しない穴も確認する。
`_` や `?` の表面上の区別と位置情報は elaboration が管理する。

## 共有と調査

`Environment::boundary` は package の検査開始時の宣言集合を記録し、`export_since` は追加された宣言を明示的な ID 付きの `EnvironmentExport` にする。
定義本体、parameter、帰納型、Program datatype、反映先を保持し、依存 package の宣言は参照として扱う。
読み込みでは `reserve_definitions` と `reserve_nominals` で対応先を予約し、raw と共有する `ExpressionGraph` を `Arena::import_graph` で復元してから宣言を再配置する。
`Environment::import_export` は参照先と反映表を検証して宣言を公開する。
部分成果物が重なる場合は、予約済み ID の宣言と式が一致することを確認して共有し、新しい宣言だけを追加する。

式の export は根から到達するノードを一度ずつ、子が先になる順序で保存する。
依存 package が所有するノードは外部参照を通じて共有し、import は現在の arena の interning を利用する。
式の読み込み失敗時は追加ノードと ID 対応表を戻し、宣言の読み込み失敗時は既存の宣言表を保持する。
kernel 宣言に到達する未解決メタ変数は export 境界で検出する。
raw の宣言参照にも用いる `Meta` ノードの identity は、frontend の対応表と `reserve_metas` によって別途再配置する。

束縛を含む構造走査は `Arena::map_children` に集約する。
環境は推論・弱頭簡約・conversion・文脈・型の shift・同時代入を共有し、`cache_counts` で件数を取得できる。
上限に達した共有表は、再利用されたエントリを優先して最大四分の三まで保持し、残りを新しい結果のために空ける。
定義登録で生じた一時ノードと共有表は、生存する宣言・メタ変数・診断・read snapshot を保って整理する。
共有表は直列化せず、復元後に再計算する。
`reduction::first_difference` は簡約後に異なる部分項とその経路を返す。
計測方法は [利用方法](../USAGE.md#診断と計測) を参照。
