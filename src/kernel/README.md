# Sort-indexed kernel

Set・Prop・Value・Computation のそれぞれに term/type/kind を持ち、十二個の arena handle で表す。
各系列は `SetTerm` / `PropTerm` / `ValueTerm` / `ComputationTerm` のように命名し、
対応する `*Node` と `*Form` を持つ。Set・Value・Computation の node は自然数の `level` を持ち、
Prop の node は level を持たない。Set と Prop の区別は handle の型で固定する。
handle は作成した `Environment::arena()` 内で使う。

arena は各 family の型付き `*Node` を直接保持する。`Op` と汎用の子配列への
変換層は持たず、型検査・簡約・reflection は `*Form` の名前付きフィールドを
pattern match する。同一構造のノードは intern し、arena と interner は
`Rc` でノード実体を共有する。`Arena::get` は所有するノードのコピー、
`Arena::read` は再帰中にも保持できる共有参照を返す。

共通の束縛走査は `src/structure/traversal.rs`、構文ごとの比較は
`src/structure/comparison.rs` にある。束縛の深さは走査するフィールドごとに指定し、
ノードには保存しない。型検査の入口と走査は family ごとの関数に分けている。
複数の family に共通する product・application の規則は、名前付きの引数を
取る補助関数で実装する。`src/construction.rs` は sort によって結果の family が
決まる構文の構築を担当する。
`construction` の構築関数は front の lowering からも利用する。構築した構文の
typing premise は、引き続き `Checker` と定義登録の入口で検査する。

`syntax::Expression` は分類済み handle の直和で、共通の走査・診断に使う。
未分類の式と metavariable は front 側の `raw` 構文に属する。
Set/Prop の両方を量化・適用する箇所には `LogicalTerm` / `LogicalType` / `LogicalKind`、
`SetArgument` / `PropArgument` と `SetExpression` / `PropExpression` も分離し、
両者の帰納型引数や消去には、それらを包む `LogicalArgument` / `LogicalExpression` を使う。
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
`ProdTerm` / `ProdType`、`LambdaTerm` / `LambdaType`、`AppTerm` / `AppType` は
binder と引数の family を区別する。外部から渡した rule・index は checker が再検査する。
Set/Prop と Program の context は別々で、各 context 内の term/type binder は
同じ de Bruijn telescope を使う。型代入は項の型注釈も辿る。

## 検査と登録

`Checker` は公開の推論入口で context の well-formedness も検査する。
`infer_set_term` / `infer_prop_term` / `infer_value_term` / `infer_computation_term` の
推論結果はそれぞれの type である。各系列に `infer_*_type` と `check_*_kind` も用意する。
kind formation の右辺には `Classifier::Upper` を使う。

`Environment::register_definition` は検査成功後に登録する。名前付き定義にする際は
局所変数を lambda で束縛し、module parameter は名前付き参照で表す。
`register_datatype` は parameter kind・field level・strict positivity を検査し、
Set の鏡像を生成する。鏡像が既にある場合は宣言との一致を検査する。

front の module はパラメーター付き名前空間であり、import は front の名前空間への
束縛になる。引数を宣言の型と本体へ同時・捕獲回避代入し、kernel へ適用ノードは渡さない。
元宣言と convertible な引数が同じなら宣言 ID を再利用する。帰納型 ID の同一性は front
で確定するため、kernel の conversion に module 専用の規則はない。
未使用の元宣言も検査し、特殊化した宣言は必要になったときに代入・検査する。

式中には `DefId` 参照を持たず、`Arena::annotated(body, classifier)` で作る共有ノードを
使う。`DefId` は名前や検査済み宣言の登録キーとしてのみ残る。`Annotated` の推論は
本体を注釈に対して検査した上で宣言した classifier を返し、conversion は本体に透過的。
型を弱めて宣言した定義でも、利用側でその注釈を失わない。
代入・変数シフト・閉性判定は注釈も辿る。node の共有は arena の interning による。

型引数を局所 context に持つ関連定義は `register_definition_template` で
body・classifier・context と、Program 定義の Set 側への反映を検査する。
利用時は front が明示的な型引数を本体と型へ代入し、通常の注釈付きノードにする。
検査済みテンプレートは kernel 環境の寿命中保持され、front の lowering を作り直しても
同じ ID を再検査しない。

Program の型演算子と多相 computation は value/computation 両方の kind を量化できる。
Program type/kind は value に依存できない。level は non-cumulative である。

## Reflection と評価

`reflection::reflect_kind`・`reflect_type`・`reflect_term` は同じ level の Set 側へ写す。
Program の `run` は accessibility 証明を、`runCase` はさらに遷移の等式証明を
項自身に保持する。型検査は反映した context で証明も検査し、reflection はその証明を引き継ぐ。
reflection は Program 項が保持する証明 premise を引き継いで Set 項を直接導出する。
定義登録と Box の入口では、導出した反映項を反映後の型に対して検査する。
閉性の検査は名前付き定義の本体も辿る。

`calculus::substitute_with_reflection` は Program の引数を証明中では Set 側へ反映して代入する。
環境を受け取らない `substitute` は反映が不要な構文用である。`shift`、module parameter 置換、ID の再割当ても
family と index を保つ。`convertible` は同一 family・level 内の比較であり、
Program type/kind の型 beta も扱う。証明を記録する内部注釈は型検査したうえで
計算上の比較から除外する。

`calculus::evaluate` は fuel を受け取り `Normal` または `OutOfFuel` を返す。
Program value 自身は step せず、computation は定められた評価位置で簡約する。
`normalize` と `whnf` は上限を超えた場合にエラーを返す。

`src/tests.rs` に多相 identity、computation 型の量化、型適用後の level、
Box / boxed type application、datatype の反映、positivity と拒否例を収録している。
