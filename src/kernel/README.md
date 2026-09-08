# Sort-indexed kernel

`stratification4.md` の term/type/kind を九つの arena handle で表す。
Set/Prop の node は `SetSort`、Program の node は自然数の `level` を持つ。
handle は作成した `Environment::arena()` 内で使う。

`syntax::Expression` は分類済み handle の直和で、共通の走査・診断に使う。
未分類の式と metavariable は front 側の `raw` 構文に属する。

## 型演算子の例

```rust
use kernel::{check::Checker, environment::Environment, ids::SymbolId,
             sort::{BaseSort, ProductRule, SetSort, Sort}, syntax::*};

let env = Environment::new();
let arena = env.arena();
let kind = arena.alloc(SetKindNode {
    sort: SetSort::Set(0), form: SetKindForm::Base,
});
let body = arena.alloc(SetTypeNode {
    sort: SetSort::Set(0), form: SetTypeForm::Bound { index: 0 },
});
let rule = ProductRule::new(
    Sort::Upper(BaseSort::Set(0)), Sort::Upper(BaseSort::Set(0)),
).unwrap();
let identity = arena.alloc(SetTypeNode {
    sort: SetSort::Set(0),
    form: SetTypeForm::LambdaType {
        rule, var: SymbolId::ANONYMOUS, domain: kind, body,
    },
});
let inferred_kind = Checker::new(&env, vec![]).infer_type(identity).unwrap();
```

`ProductRule` は domain・body・result の三つの sort を持つ。
`ProdTerm` / `ProdType`、`LambdaTerm` / `LambdaType`、`AppTerm` / `AppType` は
binder と引数の family を区別する。外部から渡した rule・index は checker が再検査する。
Set/Prop と Program の context は別々で、各 context 内の term/type binder は
同じ de Bruijn telescope を使う。型代入は項の型注釈も辿る。

## 検査と登録

`Checker` は公開の推論入口で context の well-formedness も検査する。
term の推論結果は type、type constructor の推論結果は kind である。
kind formation の右辺には `Classifier::Upper` を使う。

`Environment::register_definition` は検査成功後に登録する。名前付き定義にする際は
局所変数を lambda で束縛し、module parameter は名前付き参照で表す。
`register_datatype` は parameter kind・field level・strict positivity を検査し、
Set の鏡像を生成する。鏡像が既にある場合は宣言との一致を検査する。

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

`stratified/tests.rs` に多相 identity、computation 型の量化、型適用後の level、
Box / boxed type application、datatype の反映、positivity と拒否例を収録している。
