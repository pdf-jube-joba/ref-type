# Sort-indexed kernel

Set・Prop・Value・Computation のそれぞれに term/type/kind を持ち、十二個の arena handle で表す。
各系列は `SetTerm` / `PropTerm` / `ValueTerm` / `ComputationTerm` のように命名し、
対応する `*Node` と `*Form` を持つ。Set・Value・Computation の node は自然数の `level` を持ち、
Prop の node は level を持たない。Set と Prop の区別は handle の型で固定する。
handle は作成した `Environment::arena()` 内で使う。

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

front の module instance は、生成時には仮想名前空間と安定した宣言 ID だけを確保する。
定義・帰納型・datatype は参照時に module 引数の代入と global ID の付け替えを行い、
成功した結果を instance ごとにキャッシュする。lowering の全件走査は実体化済みの
instance 宣言だけを対象とするが、元 module の宣言は未使用でも従来どおり全件を検査する。
実体化した宣言も kernel の通常の登録・検査 API を通り、instance が異なれば同じ引数でも
帰納型 ID は共有しない。

型引数を局所 context に持つ関連定義は、閉じた `Constant` としては登録せず、
`register_definition_template` で body・classifier・context・certificate を検査する。
検査済みテンプレートは kernel 環境の寿命中保持され、front の lowering を作り直しても
同じ ID を再検査しない。

Program の型演算子と多相 computation は value/computation 両方の kind を量化できる。
Program type/kind は value に依存できない。level は non-cumulative である。

## Reflection と評価

`reflection::reflect_kind`・`reflect_type`・`reflect_term` は同じ level の Set 側へ写す。
部分的な `run` を含む Program には `reflect_with_certificate` で証明引数を補う。
certificate の構造的な対応と Set typing は別々の検査で、定義登録と Box の入口では
両方を要求する。閉性の検査は名前付き定義の本体も辿る。

`calculus::substitute`、`shift`、module parameter 置換、ID の再割当ては
family と index を保つ。`convertible` は同一 family・level 内の比較であり、
Program type/kind の型 beta も扱う。証明を記録する内部注釈は型検査したうえで
計算上の比較から除外する。

`calculus::evaluate` は fuel を受け取り `Normal` または `OutOfFuel` を返す。
Program value 自身は step せず、computation は定められた評価位置で簡約する。
`normalize` と `whnf` は上限を超えた場合にエラーを返す。

`src/tests.rs` に多相 identity、computation 型の量化、型適用後の level、
Box / boxed type application、datatype の反映、positivity と拒否例を収録している。
