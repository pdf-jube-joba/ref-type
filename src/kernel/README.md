# Sort-indexed kernel

Set・Prop・Value・Computation のそれぞれに term/type/kind を持ち、十二個の arena handle で表す。
各系列は `SetTerm` / `PropTerm` / `ValueTerm` / `ComputationTerm` のように命名し、対応する `*Node` と `*Form` を持つ。
Set・Value・Computation の node は自然数の `level` を持つ。
Set と Prop の区別は handle の型で固定する。
handle は作成した `Environment::arena()` 内で使う。

arena は各 family の型付き `*Node` を `Rc` で保持し、interner はノードの ID を保持する。
型検査・簡約・reflection は `*Form` の名前付きフィールドを pattern match する。
同一構造のノードは intern する。
`Arena::get` は所有するノードのコピー、`Arena::read` は再帰中にも保持できる共有参照を返す。

共通の束縛走査は `src/structure/traversal.rs`、構文ごとの比較は `src/structure/comparison.rs` にある。
束縛の深さは走査するフィールドごとに指定する。
型検査の入口と走査は family ごとの関数に分けている。
複数の family に共通する product・application の規則は、名前付きの引数を取る補助関数で実装する。
`src/construction.rs` は sort によって結果の family が決まる構文の構築を担当する。
`construction` の構築関数は elaboration の lowering からも利用する。
構築した構文の typing premise は、`Checker` と宣言登録の入口で検査する。

`syntax::Expression` は分類済み handle の直和で、共通の走査・診断に使う。
未分類の式と metavariable は elaboration 側の `raw` 構文に属する。
Set/Prop の両方を量化・適用する箇所には `LogicalTerm` / `LogicalType` / `LogicalKind`、`SetArgument` / `PropArgument` と `SetExpression` / `PropExpression` を使う。
帰納型引数や消去には、それらを包む `LogicalArgument` / `LogicalExpression` を使う。
証明専用の構文は `PropTermForm`、命題専用の構文は `PropTypeForm` に属する。

## 型演算子の例

```rust
use kernel::{check::Checker, environment::Environment, ids::SymbolId,
             sort::{BaseSort, ProductRule, Sort}, syntax::*};

let env = Environment::new();
let arena = env.arena();
let kind = arena.alloc(SetKindNode {
    level: 0, form: SetKindForm::Base,
});
let body = arena.alloc(SetTypeNode {
    level: 0, form: SetTypeForm::Bound { index: 0 },
});
let rule = ProductRule::new(
    Sort::Upper(BaseSort::Set(0)), Sort::Upper(BaseSort::Set(0)),
).unwrap();
let identity = arena.alloc(SetTypeNode {
    level: 0,
    form: SetTypeForm::LambdaType {
        rule, var: SymbolId::ANONYMOUS, domain: kind, body,
    },
});
let inferred_kind = Checker::new(&env, vec![]).infer_set_type(identity).unwrap();
```

`ProductRule` は domain・body・result の三つの sort を持つ。
`ProdTerm` / `ProdType`、`LambdaTerm` / `LambdaType`、`AppTerm` / `AppType` は binder と引数の family を区別する。
外部から渡した rule・index は checker が再検査する。
Program の型演算子と多相 computation は value/computation 両方の kind を量化できる。
Program type/kind は value に依存できず、level は non-cumulative である。

## Context と宣言の検査

`Context` は `Binding { var, classifier }` を外側から並べた de Bruijn telescope で、各 classifier はそれ以前の binding の下に置く。
式は `Bound { index }` で変数を参照し、index 0 が最も内側の binding を指す。
`SymbolId` は表示用の binder ラベルであり、変数の同一性は index で決まる。

Program の変数と、その反映を使う Set/Prop の仮定を同じ telescope に並べられる。
Set/Prop の変数参照が Program の binding を指すときは、その classifier を Set 側へ反映して推論する。
`reflection::reflect_context` は Program の binding を反映し、Set/Prop の binding はそのまま引き継ぐ。

`Checker` は公開の推論入口で context の well-formedness も検査する。
`infer_set_term` / `infer_prop_term` / `infer_value_term` / `infer_computation_term` の推論結果はそれぞれの type である。
各系列に `infer_*_type` と `check_*_kind` も用意する。
kind formation の右辺には `Classifier::Upper` を使う。

`Environment::register_definition(id, Definition { context, body, classifier })` は context・body・classifier を検査してから保持する。
body と classifier はその context の下で解釈する。
Program 定義は Set 側へ反映した body・classifier・context も検査する。
利用側の context に定義を移すときは、`calculus::instantiate_telescope` で引数を同時代入する。

`InductiveSpec::parameters` と `ProgramDatatype::parameters` も通常の telescope である。
帰納型・constructor の参照はこの telescope に対応する引数を持つ。
`register_inductive` は形成規則・constructor の戻り先・strict positivity を検査する。
`register_datatype` は parameter kind・field level・strict positivity を検査し、Set の鏡像を生成する。
鏡像が既にある場合は宣言との一致を検査する。

module の構成・名前解決・import の特殊化は elaboration が所有する。
elaboration の lowering は宣言が参照する module parameter と、その型が必要とする parameter を集め、依存順に通常の context へ変換する。
帰納型ではそれらを parameter telescope に加える。
元宣言と特殊化した宣言の対応、および帰納型の同一性も elaboration で確定する。

## GlobalId と式のラベル

`GlobalId(pub u64)` は呼び出し側が割り当てる不透明なラベルである。
名前・source location・module などへの対応表は呼び出し側が所有する。
`Environment` 内では定義の登録キーにも使い、同じ ID の重複登録をエラーにする。
複数の環境や再実行にまたがる ID の安定性は呼び出し側が管理する。

`Arena::identified` は `Annotated` ノードの `global: Option<GlobalId>` に ID を保持する。
`Arena::annotated` はラベルを省略した型注釈を作る。
注釈は Set/Prop の term/type/kind と Program の term/type に付けられる。

```rust
use kernel::{check::Checker, environment::{Classifier, Environment},
             ids::GlobalId, sort::BaseSort, syntax::*};

let env = Environment::new();
let arena = env.arena();
let body = arena.alloc(SetKindNode { level: 0, form: SetKindForm::Base });
let classifier = Classifier::Upper(BaseSort::Set(0));
let expression = arena.identified(GlobalId(42), body.into(), classifier).unwrap();
assert_eq!(arena.global_id(expression), Some(GlobalId(42)));
Checker::new(&env, vec![]).check(expression, classifier).unwrap();
```

`Arena::global_id` は渡した式の最外側の注釈ラベルを返す。
elaboration は定義の参照をこの注釈で包むため、利用側は展開済みの本体からも参照元を追える。
同じ定義に異なる引数を代入した式は、同じラベルを持ち得る。

ノードの interning と handle の `Eq` / `Hash` はラベルも含めて区別する。
`calculus::alpha_equal` はラベルを無視して本体と classifier を比較し、conversion と簡約は注釈の本体に対して行う。
型推論は毎回必要な typing premise を検査して宣言された classifier を返すため、同じ ID を持つ別の本体にも通常の検査が適用される。
型を弱めて宣言した定義でも、利用側はその注釈を保持できる。

代入・変数シフト・reflection・帰納型 ID の再割当ては、注釈を変換するときに `GlobalId` を引き継ぐ。
簡約で注釈自体が取り除かれた場合、そのラベルも式から取り除かれる。
`printing::format_expression` の診断にもラベルを表示する。

`InductiveId(pub u64)` と `ProgramInductiveId(pub u64)` は帰納型の nominal identity で、`GlobalId` とは別の型である。
これらも呼び出し側が割り当て、kernel は同一性の比較と宣言の取得に使う。
constructor の構造が同じでも、異なる帰納型 ID は異なる型を表す。

## Reflection と評価

`reflection::reflect_kind`・`reflect_type`・`reflect_term` は同じ level の Set 側へ写す。
Program の `run` は accessibility 証明を、`runCase` はさらに遷移の等式証明を項自身に保持する。
型検査は反映した context で証明も検査し、reflection はその証明を引き継ぐ。
定義登録と Box の入口では、導出した反映項を反映後の型に対して検査する。
Box が保持する Program 構文は computation type と computation に限る。
閉性判定は注釈の本体と classifier も辿る。

`calculus::substitute_with_reflection` は Program の引数を証明中では Set 側へ反映して代入する。
`instantiate_telescope` は複数の引数を一度の走査で同時代入し、束縛の深さごとに共有部分木の結果を再利用する。
環境を受け取らない `substitute` は反映が不要な構文用である。
変数のシフト・出現判定・閉性判定は、ノードごとに保存した自由な de Bruijn index の最大値で不要な走査を省く。
帰納型 ID の再割当てはノードをキーに共有部分木の再走査を省く。
conversion 中の alpha 比較も、再帰全体で比較済みノード対の結果を共有する。
`convertible` は同一 family・level 内の比較であり、Program type/kind の型 beta も扱う。
証明を記録する内部注釈は型検査したうえで計算上の比較から除外する。

`calculus::evaluate` は fuel を受け取り `Normal` または `OutOfFuel` を返す。
Program value 自身は step せず、computation は定められた評価位置で簡約する。
`normalize` と `whnf` は上限を超えた場合にエラーを返す。
`whnf` は関数への連続した適用をまとめ、対応する lambda の引数を同時代入して中間ノードの生成を抑える。

## 共有と診断

宣言登録の検査で作った一時ノードは、検査が終わるとまとめて回収する。
推論と弱頭簡約のキャッシュは、キーと結果の両方が検査開始前のノードだけを参照するエントリーを残す。
検査開始前の handle と、直接 `Checker` から返された handle は保持する。
datatype の鏡像は一時ノードの回収後に生成・登録する。

`Arena::node_counts`、`Environment::cache_counts`、`Environment::declaration_node_count` で保持量を調べられる。
`printing::format_expression` は深さとノード数を制限して構文を表示し、tracing は宣言検査などの実行経路を記録する。
`src/tests.rs` に型演算・reflection・positivity・context・注釈ラベル・共有と代入の検査を収録している。
