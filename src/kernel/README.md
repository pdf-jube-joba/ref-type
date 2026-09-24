# Sort-indexed kernel

Set・Prop・Value・Computation のそれぞれに term/type/kind を持ち、十二個の arena handle で表す。
各系列は `SetTerm` / `PropTerm` / `ValueTerm` / `ComputationTerm` のように命名し、
対応する `*Node` と `*Form` を持つ。Set・Value・Computation の node は自然数の `level` を持ち、
Prop の node は level を持たない。Set と Prop の区別は handle の型で固定する。
handle は作成した `Environment::arena()` 内で使う。

arena は各 family の型付き `*Node` を `Rc` で保持し、interner はノードの ID を保持する。
型検査・簡約・reflection は `*Form` の名前付きフィールドを pattern match する。
同一構造のノードは intern する。
`Arena::get` は所有するノードのコピー、`Arena::read` は再帰中にも保持できる共有参照を返す。

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

`Environment::register_definition` は閉じた body と classifier を検査して登録する。
開いた宣言は `register_definition_template` で context とともに検査する。
外側の context は `push_binding` が既存 prefix で classifier を検査した後に拡張し、`Ambient { level }` が de Bruijn level で参照する。
式内の `Bound { index }` は、局所 binder からの de Bruijn index を表す。
外側の context を拡張しても、登録済み template の level は変化しない。
`register_datatype` は parameter kind・field level・strict positivity を検査し、Set の鏡像を生成する。
鏡像が既にある場合は宣言との一致を検査する。

宣言登録の検査で作った一時ノードは、検査が終わるとまとめて回収する。
推論と弱頭簡約のキャッシュは、キーと結果の両方が検査開始前のノードだけを参照するエントリーを残す。
検査開始前の handle と、直接 `Checker` から返された handle は保持する。
datatype の鏡像は一時ノードの回収後に生成・登録する。

`GlobalId`、`InductiveId`、`ProgramInductiveId` は所有環境で発行する opaque な identity である。
再帰 spec は先に identity を予約して組み立て、登録時の検査に成功してから公開する。
semantic item や instance と identity の対応は elab の bridge が所有する。

定義の利用には `Arena::annotated(body, classifier)` で作る共有ノードを使う。
`GlobalId` は検査済み宣言の登録キーである。
`Annotated` の推論は本体を注釈に対して検査した上で宣言した classifier を返し、conversion は本体に透過的。
型を弱めて宣言した定義でも、利用側でその注釈を失わない。
代入・変数シフト・閉性判定は注釈も辿る。node の共有は arena の interning による。

template の登録では body・classifier・context と、Program 定義の Set 側への反映を検査する。
`instantiate_template` は外側の文脈への引数を検査し、body・classifier・局所 context に捕獲回避同時代入を行い、利用側の context で再検査する。
型引数の特殊化は bridge でも行い、検査された本体と型から注釈付きノードを作る。

`Environment::transfer` は公開順に context と宣言を新しい環境へ移送し、再検査する。
arena handle と nominal identity は再割当てし、DAG の共有と datatype・mirror の対応を保つ。
成功時に返す `Relocation` は旧 handle・ID から新しい環境への対応を持つ。
移送先は独立した所有権を持ち、移送元を破棄した後も検査できる。

Program の型演算子と多相 computation は value/computation 両方の kind を量化できる。
Program type/kind は value に依存できない。level は non-cumulative である。

## Reflection と評価

`reflection::reflect_kind`・`reflect_type`・`reflect_term` は同じ level の Set 側へ写す。
Program の `run` は accessibility 証明を、`runCase` はさらに遷移の等式証明を
項自身に保持する。型検査は反映した context で証明も検査し、reflection はその証明を引き継ぐ。
reflection は Program 項が保持する証明 premise を引き継いで Set 項を直接導出する。
定義登録と Box の入口では、導出した反映項を反映後の型に対して検査する。
Box が保持する Program 構文は computation type と computation に限る。
閉性の検査は名前付き定義の本体も辿る。

`calculus::substitute_with_reflection` は Program の引数を証明中では Set 側へ反映して代入する。
`instantiate_telescope` は複数の引数を一度の走査で同時代入し、束縛の深さごとに共有部分木の結果を再利用する。
変数のシフト・出現判定は、ノードごとに保存した自由な de Bruijn index の最大値で不要な走査を省く。
外側の文脈への代入はノードと束縛の深さ、ID 再割当てと閉性判定はノードをキーに共有部分木の再走査を省く。
conversion 中の alpha 比較も、再帰全体で比較済みノード対の結果を共有する。
環境を受け取らない `substitute` は反映が不要な構文用である。
`shift`、`substitute_ambient`、ID の再割当ては family と universe level を保つ。
`ReflectedAmbient` への Program 引数は Set 側に反映してから代入する。
`convertible` は同一 family・level 内の比較であり、Program type/kind の型 beta も扱う。
証明を記録する内部注釈は型検査したうえで計算上の比較から除外する。

`calculus::evaluate` は fuel を受け取り `Normal` または `OutOfFuel` を返す。
Program value 自身は step せず、computation は定められた評価位置で簡約する。
`normalize` と `whnf` は上限を超えた場合にエラーを返す。
`whnf` は関数への連続した適用をまとめ、対応する lambda の引数を同時代入して中間ノードの生成を抑える。

`src/tests.rs` に多相 identity、computation 型の量化、型適用後の level、
Box / boxed type application、datatype の反映、positivity と拒否例を収録している。
