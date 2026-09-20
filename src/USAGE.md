## フォルダ構成
- kernel: ほぼ理論通りの実装
  - 理論側の言語
  - type-check / type-infer
  - checker
- front: 言語処理系
  - 実装側の言語
  - parser
  - elaboration

## ソースファイルと module

ソースファイルの拡張子は `.ref`。CLI にはルートファイルを一つ渡す。

```sh
cargo run -- path/to/root.ref
```

typing rule の呼び出しを木構造で確認する場合は `--trace` を付ける。

```sh
cargo run -- path/to/root.ref --trace
```

`--parse-only` を付けると、ルートファイルと外部 module を front 側の構文に変換できるかだけを確認する。

```sh
cargo run -- path/to/root.ref --parse-only
```

typing は通常の `tracing` span/event として記録される。ログレベルを細かく指定する
場合は、たとえば `RUST_LOG=ref_type::typing=debug` を利用できる。通常実行では
typing span は無効で、型検査に必要な証明は各項の部分項として検査される。

本体を別ファイルに置く module は `\module Name;` と宣言する。ルートファイルと
同じディレクトリの `Name.ref` が module 本体として読み込まれる。外部ファイルには
`\module Name { ... }` を繰り返さず、module item を直接記述する。

子 module の配置は論理 module パスに対応する。たとえば `root.ref` の
`\module Algebra;` は `Algebra.ref`、その中の `\module Group;` は
`Algebra/Group.ref` を読み込む。ファイル名の大文字と小文字は宣言と一致させる。

module は front のパラメーター付き名前空間として扱う。import は引数の代入を保持し、
その alias を起点に child module も参照できる。module 内で宣言した import alias は
その子 module からも同じ名前で参照でき、子側の同名 import がある場合はそちらを優先する。
各 module path には `[]` が必要で、parameter は名前と宣言順を一致させてすべて指定する。
module argument 内では `_`・`?` による推論を行わない。

```text
\import \root.Parent[A := Nat] \as P;
\import P.Child[x := value] \as C;
```

`C` は `P` の代入を引き継ぐ。同じ元宣言に convertible な引数を渡す import は、
繰り返しても同じ定義・帰納型 ID を使う。外側の module の引数を代入した場合も、
元宣言と合成した引数から ID を選び直す。異なる元宣言の帰納型や、convertible でない
引数を持つ帰納型は別の型になる（使われない引数や証明引数も区別に含む）。

通常の定義は kernel では本体と宣言した型を保持する `Annotated` ノードになる。
注釈は型推論に使い、conversion では本体を比較する。module の代入は front で完了し、
kernel の関数適用や product rule は追加しない。

## 公理

kernel が提供する公理は proof term として使う。各引数は通常の typing rule で検査される。

```text
\axiom:setext(A, B, forward, backward)
\axiom:funext(f, g, pointwise)
\axiom:classicalIndefiniteChoice(X, Family, inhabited)
```

`setext` は同じ `Power(X)` の要素と双方向の包含証明を、`funext` は同じ関数型の
二項と各点での等号を要求する。`classicalIndefiniteChoice` は `Family: X -> Set` と
`\forall (x: X) -> exists (Family x)` から `exists (\forall (x: X) -> Family x)` を返す。

## Program の構文

Program の関数型は `A ~> C`、ラムダは `\cfun (x: A) => computation`。
値の型と計算の型は区別し、`\F(A)` と `\U(C)` は従来どおり使う。
計算の適用は `function value` と書き、左結合する。引数は値であり、
計算結果を渡す場合は先に `\bind` で受け取る。

```text
\module Example(A: \VType, a: A) {
  \definition identity(x: A): \F(A) := \return x;
  \definition result: \F(A) :=
    \let x: A := a \in
    \bind y: A <- identity x \in
    \return y;
}
```

Program の値型と値は module parameter にできる。具体化するときも Program 構文を渡す。

```text
\module Source(A: \VType, a: A) {
  \definition value: A := a;
}
\module Consumer {
  \inductive Unit: \VType := | unit: Unit; ;
  \import \root.Source[A := Unit, a := Unit::unit] \as S;
  \vcheck S.value: Unit;
}
```

Set 側では名前に `^` を付けて反映を明示する。`Unit^: \Set`、
`Unit^::unit: Unit^`、`S.value^: Unit^` となる。Program の module parameter
`A: \VType, a: A` の反映も `A^: \Set, a^: A^` と書く。
型のパラメータも Set 側で指定し、例えば `Pair^[Unit^]` とする。

`\let` は値、`\bind` は計算結果を束縛する。型注釈は必須で、`_` を使うと
制約から補完する。解決できなければエラーになる。名前は後続部分だけで有効であり、
型注釈と右辺は外側のスコープで解釈する。`\in` の後には計算式が必要で、
その本体を右端まで読む。束縛式を適用の引数に置く場合は括弧で囲む。
同じ束縛を文として並べる Program ブロックも使える。

```text
\definition result: \F(A) := \program {
  \let x: A := a;
  \bind y: A <- identity x;
  \return y;
};
```

Program ブロックは `\program { ... }` の中に `\let`・`\bind` の文を順に並べ、値を返す
`\return value;` で終える。各束縛名は後続の文だけで有効になる。
`\definition f(x: A, y: B): C := body;` は、型 `A ~> B ~> C` と
本体 `\cfun (x: A) (y: B) => body` に展開する。
`\definition` は宣言した型と本体から Set/Prop、Program value、Program computation を判定する。

`\force suspended` は thunk を実行し、`\thunk (computation)` は計算を値に包む。
`\force f x` は `(\force f) x`。thunk の関数値を適用するときは `\force` を明示する。
カリー化された計算の途中結果も `\bind` で明示的に受け取る。
`return`・`thunk`・`force`・`bind` の自動挿入は行わない。
場合分けは `\match value \in Datatype \with { | ctor x => computation }`。
型名は必須。分岐は次の `|` または `}` で区切り、末尾に `;` は付けない。
引数なしの分岐は `| ctor => computation` とする。`\case`・`\tmatch` の分岐も同様。
論理側の場合分けは `\case value \in Datatype \return motive { | ctor => branch }` とする。
旧 `\capp`・`\do` および `\CFun`・`\clam`・`\sequence`・`\vlet`・`\vcase` は受け付けない。

論理側の束縛は `\fun (x: A) => body` と `\forall (x: A) -> B`。
束縛のない `A -> B` はそのまま使える。レコード生成は
`\record T { field := value }` と書く。論理／Program 共通の構文であり、Program では次のように使う。

```text
\record Pair[A: \VType]: \VType := { first: A, second: A };
\definition Pair(A: \VType)::first_again: Pair[A] ~> \F(A) := Pair[A]::first;
\definition Pair(A: \VType)::get_first: \U(Pair[A] ~> \F(A)) :=
  \thunk (Pair[A]::first);
```

Program record の field は非依存・非再帰の値型とする。構築は
`\record Pair[A] { first := a, second := b }`、field の取得は
`Pair[A]::first pair` と書く。取得結果は `\F(A)` なので、
後続の計算で使うには `\bind` で受け取る。
Program の inductive／structure には
`\definition Type(A: \VType)::item` として型関連 item を定義できる。
型引数は `Type[A]::item` で指定し、省略や `_` は文脈から推論する。

マクロ内の `(...)` はマクロ列であり、通常式の埋め込みには `{ ... }` を使う。
詳細は [構文](../doc/book/src/coding/syntax.md) を参照。

## 実行と診断

```sh
cargo run -p cli -- lib/root.ref
cargo run -p cli -- lib/root.ref --trace
RUST_LOG=ref_type=trace cargo run -p cli -- lib/root.ref
```

`--trace` は Set/Prop・Program の型検査、定義登録、反映、正規化・評価のログを木構造で表示します。
`RUST_LOG=ref_type=trace` では束縛の出入りと簡約ステップも表示します。
特定の処理だけを追う場合は `RUST_LOG=ref_type::typing::program=debug` や
`RUST_LOG=ref_type::reduction=trace` を指定できます。`RUST_LOG` は `--trace` の既定フィルタより優先されます。
ログとエラーは標準エラー出力へ書き込みます。ファイルへ保存する場合は `2> kernel.log` を付けます。

`RUST_LOG=ref_type::typing=error` では型検査の失敗時の診断に絞って表示できます。
front の型不一致には局所文脈・対象の項・推論した型・要求された型を、等号の carrier が
一致しない場合には左右の項と型を表示します。式中の `#0` は最も内側の束縛を指します。

宣言ごとの処理時間と定義内の各段階を調べる場合は、`REF_TYPE_PROFILE_DECLARATIONS=1` を指定します。
値を宣言名の一部にすると、一致する宣言だけを表示します。
where 節の局所定義の検査時間は `REF_TYPE_PROFILE_LOCAL_DEFINITIONS=1` で表示し、同様に名前で絞り込めます。

```sh
REF_TYPE_PROFILE_DECLARATIONS=fieldMulAssocNN cargo run -p cli -- lib/root.ref
REF_TYPE_PROFILE_LOCAL_DEFINITIONS=right cargo run -p cli -- lib/root.ref
```

未解決ゴールには文脈・要求される型・制約を表示します。ファイルから読み込んだ宣言のエラーには
元ファイル・行・列とソースの抜粋を付けます。型検査の位置表示は宣言単位、構文エラーはトークン単位です。
外部モジュールのパラメータは宣言元ファイル、本文は外部ファイルの位置を使います。

kernel の `Environment::register_definition` は、分類済みの本体・classifier・文脈を
検査してから指定された `DefId` に登録します。Program の反映証明を指定した場合は、
その Set typing と Program 本体との構造的な対応も検査します。

front は未分類構文で elaboration と meta の解決を行い、分類・level・product rule を
付けた構文を kernel に渡します。`GlobalEnvironment::kernel_env()` が検査済みの環境です。
`crate_env()` は elaboration・macro・診断・raw 評価に使う front 側の環境を返します。
module 実体化で生じた定義も新しい ID で kernel の登録検査を通します。

```sh
cargo test --workspace --offline
```

`tests/ng` の各ファイルには `/* expect-error: 診断に含まれる文字列 */` を書きます。
複数指定した場合はすべて照合します。終了コード 1 と診断を確認し、panic やシグナル終了は失敗として扱います。

## Sort-index と level

Set/Prop の kernel 構文は `SetTerm`・`SetType`・`SetKind`、Program は
`Value`・`Computation` とそれぞれの type・kind に分かれています。
`SetType` は型演算子も含みます。term の型に使う場合は、その kind が基底 sort であることを検査します。

level は non-cumulative です。たとえば `A: \Set(0)` を `\Set(1)` の要素として
暗黙に使うことはできません。product の level は `max` の規則で決まり、
多相関数の型適用では適用結果の level が関数自身より小さくなる場合があります。
RunStep recursor の branch と結果の level も、それぞれの product rule に従います。

既存の Program 表面構文は level 0 に対応します。`\Box`・`\box`・`\Force` が
受け取る Program 構文は computation type / computation に限られます。value を
Box に入れる場合は `\F(A)` と `\return(value)` を使います。Program の型演算子、
多相性、level 付き Box、boxed type application は kernel API から利用できます。
API の例は [kernel の説明](kernel/README.md) を参照してください。
`\eval`・`\normalize` による未分類の式の簡約は front が引き続き処理します。
