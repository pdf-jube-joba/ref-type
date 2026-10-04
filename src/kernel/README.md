# PTS kernel

sort・型・項・証明は共通の `syntax::Expression` と `syntax::Node` で表す。
`Expression` は所有する `Arena` 内の intern 済み handle であり、子の項と binder の型も同じ handle を使う。
`Arena::get` はノードのコピー、`Arena::read` は構造操作の間も保持できる共有参照を返す。
型規則は `check`、束縛と代入は `calculus`、簡約と評価は `reduction`、reflection は `reflection` にある。

`Context` は `Binding { var, ty }` を外側から並べた telescope とする。
`Bound(0)` は最も内側の変数を表し、各 binding の型はそれ以前の文脈で解釈する。
`SymbolId` は表示用の名前であり、alpha 等価性は binder の名前を除いて比較する。
型規則は `sort::Sort` の公理と product 関係を使い、Program の型には型変数への依存条件を課す。
論理側と Program 側の lambda・適用は `Mode` で評価規則を区別する。

## 型推論と定義

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

`Checker::infer` と `Checker::check` は文脈の形成を確認し、対象・期待型・文脈に未解決メタ変数があれば `Error::Unresolved` を返す。
`Environment::register_definition` は `MetaContext::finish` と厳密な型検査を行い、検証済みの `Definition { context, ty, body }` を定義 arena に保存する。
登録の戻り値が `DefinitionId` であり、参照は `Node::Definition { id, arguments }` で表す。
参照の型は宣言型への同時代入で求め、簡約時には本体へ同じ引数を代入する。
Program 定義は反映先の定義も検査して登録する。

論理 sort を domain に持つ積型は必ず論理側の型なので、適用の `Mode` 判定には domain の形成を使い、残りの関数型全体の形成を繰り返さない。
Program の domain では積型の sort で判定する。

module の parameter は、名前解決中の開いた式では `ParameterId` により参照する。
parameter の型は登録時に検査し、完成した定義は parameter を telescope と明示的な文脈引数に閉じる。
宣言名・source location・module の所属は elaboration が保持する。

`register_inductive` は arity・constructor の戻り先・sort・strict positivity を検査する。
`register_datatype` は Program の field と parameter を検査し、Set の鏡像を登録する。
Box の閉性検査は定義参照の引数も走査する。

## メタ変数と制約

`MetaContext::fresh` は宣言文脈と期待型を保持するメタ変数を作る。
`Node::Meta { id, arguments }` の引数列は、宣言文脈から出現文脈への代入を表す。
メタ変数 ID は session ごとに区別し、構文ノードは不変のまま、代入を `MetaContext` に保存する。

| 操作 | 役割 |
| --- | --- |
| `infer`・`check` | 厳密な checker と共通の型規則から制約を生成する |
| `unify` | 定義的等価性と contextual pattern の抽象化を使い、解決・保留・矛盾を返す |
| `solve_pending` | 代入や期待型の更新後に保留した判断を再実行する |
| `finish` | 全メタ変数と全検査義務の完了を確認し、残存があれば失敗する |
| `zonk` | 解決済みメタ変数に文脈引数を代入する |
| `snapshot`・`rollback` | 試行前の代入と制約を復元する |
| `restrict` | 共有する穴の文脈を共通の接頭辞へ制限する |

occurs check は代入候補・期待型・宣言文脈を通じた循環を検出する。
候補の型検査に追加情報が必要な場合は、その検査義務も完了条件に含める。
`finish` は自動生成した穴と、結果の項から到達しない穴も確認する。
reflection は未解決の Program 項を `Reflect` として保持し、代入後に簡約する。

`_`・番号付きの穴・`?` の名前と source location は elaboration の情報である。
`?` も kernel の通常のメタ変数として解き、elaboration は求まった解を含むゴールを表示する。
`?` を含む module は、ゴールの確認を求める入力として elaboration の失敗を返す。

## 共有・診断・計測

束縛の走査は `Arena::map_children` に集約し、型引数・binder 注釈・証明も変換する。
同時代入と弱頭簡約は連続する lambda の引数をまとめて処理する。
Program の評価は computation の評価位置に従う。
run の証明は検査と代入の対象であり、定義的等価性では証明を消去して比較する。

Arena はノード作成時に自由変数の最大添字とメタ変数の有無を集計する。
Checker は文脈の識別子とメタ変数の有無を binder の追加・削除に合わせて更新する。
完成した項の推論・弱頭簡約・変換可能性を環境にキャッシュする。
未解決メタ変数を含む判断は、代入状態を参照して計算する。
型不一致のエラーは文脈・対象・推論型・期待型と共有 Arena を保持する。
ノード数とキャッシュ件数は環境の統計 API から取得できる。

## 一時ノードと診断

定義登録の検査で生じた一時ノードは、登録済み定義、メタ変数の文脈・型・代入・制約、型不一致の診断、保持中の read snapshot から到達する項を生存対象として回収する。
回収した handle の番号は再利用せず、関連する推論・簡約・conversion キャッシュも整理する。
`cache_counts` は推論・弱頭簡約・conversion・文脈の共有件数を返す。
`reduction::first_difference` は、頭部簡約後に異なる部分項とそこへの経路を返す。

メタ変数には `OriginId` を対応付けられ、`constraint_origins` で関連する由来を取得できる。
保留制約は依存するメタ変数の型・代入を追跡し、その状態が変わると再実行する。
永続キャッシュの fingerprint は `sema/build.rs` が kernel を含む Rust ソースから生成する。
