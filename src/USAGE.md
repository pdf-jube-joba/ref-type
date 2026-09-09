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

typing は通常の `tracing` span/event として記録される。ログレベルを細かく指定する
場合は、たとえば `RUST_LOG=ref_type::typing=debug` を利用できる。通常実行では
typing span は無効で、型検査に必要な証明は各項の部分項として検査される。

本体を別ファイルに置く module は `\module Name;` と宣言する。ルートファイルと
同じディレクトリの `Name.ref` が module 本体として読み込まれる。外部ファイルには
`\module Name { ... }` を繰り返さず、module item を直接記述する。

子 module の配置は論理 module パスに対応する。たとえば `root.ref` の
`\module Algebra;` は `Algebra.ref`、その中の `\module Group;` は
`Algebra/Group.ref` を読み込む。ファイル名の大文字と小文字は宣言と一致させる。

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
計算の適用は `\capp(function, value)` と書く。

```text
\module Example(A: \VType, a: A) {
  \cdefinition identity: A ~> \F(A) :=
    \cfun (x: A) => \return x;
  \cdefinition result: \F(A) := \do {
    \let x: A := a;
    \bind y: A <- \capp(identity, x);
    \return y
  };
}
```

Program の値型と値は module parameter にできる。具体化するときも Program 構文を渡す。

```text
\module Source(A: \VType, a: A) {
  \vdefinition value: A := a;
}
\module Consumer {
  \inductive Unit: \VType := | unit: Unit; ;
  \import \root.Source(A := Unit, a := Unit::unit) \as S;
  \vcheck S.value: Unit;
}
```

`\let` は値、`\bind` は計算結果を束縛する。型注釈は必須で、`_` を使うと
制約から補完する。解決できなければエラーになる。名前は後続部分だけで有効であり、
型注釈と右辺は外側のスコープで解釈する。ブロック末尾には計算式が必要で、
その末尾の `;` は省略できる。

`\force suspended` は thunk を実行し、`\thunk (computation)` は計算を値に包む。
場合分けは `\case value \in Datatype { | ctor(x) => computation; }`。
旧 `\CFun`・`\clam`・`\sequence`・`\vlet`・`\vcase` は受け付けない。

論理側の束縛は `\fun (x: A) => body` と `\forall (x: A) -> B`。
束縛のない `A -> B` はそのまま使える。レコード生成は
`\record T { field := value }` と書く。論理／Program 共通の構文であり、Program では次のように使う。

```text
\structure Pair(A: \VType): \VType := { first: A, second: A };
\cdefinition Pair(A: \VType)::first_again: Pair[A] ~> \F(A) := Pair[A]::first;
\vdefinition Pair(A: \VType)::get_first: \U(Pair[A] ~> \F(A)) :=
  \thunk (Pair[A]::first);
```

Program record の field は非依存・非再帰の値型とする。構築は
`\record Pair[A] { first := a, second := b }`、field の取得は
`\capp(Pair[A]::first, pair)` と書く。取得結果は `\F(A)` なので、
後続の計算で使うには `\bind` で受け取る。
Program の inductive／structure には `\vdefinition Type(A: \VType)::item`
と `\cdefinition Type(A: \VType)::item` を定義できる。
型引数は `Type[A]::item` で指定し、省略や `_` は文脈から推論する。

マクロ内の `(...)` はマクロ列であり、通常式の埋め込みには `\expr { ... }` を使う。
詳細は [構文](../doc/book/src/coding/syntax.md) を参照。

## 実行速度の計測

```sh
cargo bench -p cli --bench performance -- --save-baseline before
# 実装を変更した後
cargo bench -p cli --bench performance -- --baseline before --save-baseline after
```

構文解析・型検査・正規化・Program 評価を計測します。
対象の絞り込みや結果の見方は [ベンチマークの手順](cli/benches/README.md) を参照してください。

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

既存の Program 表面構文は level 0 に対応します。Program の型演算子、多相性、
level 付き Box、boxed type application は kernel API から利用できます。
API の例は [kernel の説明](kernel/README.md) を参照してください。
`\eval`・`\normalize` による未分類の式の簡約は front が引き続き処理します。
