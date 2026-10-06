# gaps の最小比較サンプル

各 `.ref` の全文を playground.md に貼り付けて、1ファイルずつ検査する。
必要な宣言は各ファイルに含まれ、標準ライブラリや外部ファイルの import は不要である。
`\root.Repro[]` への参照は、同じファイル内のモジュールを具体化する。
比較する組では、下記の条件だけを変え、それ以外の宣言・入力・検査対象をそろえている。

2026-10-06、`48df21d` の処理系で全43ファイルを、それぞれ空の一時ディレクトリの `root.ref` として検査した。
構文解析は全件成功し、型検査は34件成功、9件が下記の診断で失敗した。
修正済みの項目は両側が成功する比較として残している。

名前処理の追加調査で、G05・G06 の外側の引数を渡す比較と、G09 の `\let` による射影の比較を4ファイル追加した。
追加調査時は3件成功し、`09-04-block-let.ref` は `Module import 'y' was not found` で失敗した。

G05・G06・G07・G09 は対応済みで、比較用ケースを含む全16ケースが成功する。
回帰テストは [gaps_g05_g09.rs](../../src/elaboration/tests/gaps_g05_g09.rs) にあり、複数フィールドの構造体、型の別名、連続した import、局所変数の shadowing と引数個数の診断も検査する。

2026-10-07、`7aee112` の処理系で既存47ファイルを再検査し、43件が成功した。
失敗する例は G01・G02・G08・G11 の各1件である。
さらに G14 の最小比較を3ファイル追加し、宣言ヘッダ形式と型推論を組み合わせた1件の失敗、lambda 形式と型注釈を明示した2件の成功を確認した。

G08・G14 も対応済みで、両項目の全6ケースが成功する。
回帰テストは [gaps_g08_g14.rs](../../src/elaboration/tests/gaps_g08_g14.rs) にある。
G10 は他の修正に伴って解消済みとして扱い、比較の両ケースが成功する。
修正後の全50ファイルでは47件が成功し、G01・G02・G11 の各1件が現行の規則による失敗として残る。

個別に CLI で確認する場合は、リポジトリのルートで実行する。

```sh
cargo build --locked --offline -p cli
target/debug/cli _plans/fix-md/cases/05-01-dependent-type-minimal.ref --no-cache --diagnostics compact
```

<a id="対象文書の対応"></a>

## 項目と比較対象

| 項目 | 変える条件 | 結果 |
| --- | --- | --- |
| [G01](#g01) | record の変数と具体値 | 変数で失敗、具体値で成功。 |
| [G02](#g02) | 通常の関数と contextual な定義 | 通常の関数で失敗、contextual な定義で成功。 |
| [G03](#g03) | 宣言型からの推論と明示した型注釈 | 両方成功。 |
| [G04](#g04) | 定義した型名と元の帰納型名 | 両方成功。 |
| [G05](#g05) | 部分集合の条件がモジュール引数に依存するか | 対応済み。比較用ケースも成功。 |
| [G06](#g06) | 内部の帰納型の宣言位置、内部 import の関数を使うか | 対応済み。比較用ケースも成功。 |
| [G07](#g07) | signature 全体と展開済みのフィールドを実引数にするか | 対応済み。比較用ケースも成功。 |
| [G08](#g08) | 展開される定義の穴、検査済みの名前を渡すか | 対応済み。全ケース成功。 |
| [G09](#g09) | 射影の記法、lambda の位置 | 対応済み。比較用ケースも成功。 |
| [G10](#g10) | 内部 import した型と同じスコープで定義した型 | 他の修正に伴って解消済み。両方成功。 |
| [G11](#g11) | Machine の引数と具体値 | 引数で失敗、具体値で成功。 |
| [G12](#g12) | 同じ述語の再帰定義と定数関数 | 両方成功。 |
| [G13](#g13) | 帰納型の parameter の有無 | 両方成功。 |
| [G14](#g14) | 恒等関数の宣言形式と、合同則に渡す lambda の型注釈 | 対応済み。全ケース成功。 |

<a id="g01"></a>

## G01: record eta 則

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [01-01-record-eta.ref](cases/01-01-record-eta.ref) | `s` は定義の引数。 | 失敗：`types are not convertible`。 |
| [01-02-record-eta-concrete.ref](cases/01-02-record-eta-concrete.ref) | `s` は既に定義した具体的な record。 | 成功。 |

差分は `eta` の `(s: Record)` の有無だけである。
両側とも `s = Record { field := s.field }` を `refl(s)` で検査する。
`refl` による定義的な eta の比較である。

<a id="g02"></a>

## G02: 命題を条件とする集合値の構成

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [02-01-proof-function.ref](cases/02-01-proof-function.ref) | `choose: P -> A := \fun (h: P) => a`。 | 失敗：`no product rule for these sorts`。 |
| [02-02-proof-contextual.ref](cases/02-02-proof-contextual.ref) | `choose(h: P): A := a`。 | 成功。 |

命題 `P`、集合 `A`、返す値 `a` は共通で、証明引数を通常の関数にするか contextual な定義にするかだけを変える。

<a id="g03"></a>

## G03: 宣言された型からの証明引数の推論

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [03-01-infer-projection.ref](cases/03-01-infer-projection.ref) / [03-02-explicit-projection.ref](cases/03-02-explicit-projection.ref) | 射影する `value` の注釈を `_` / `Witness` にする。 | 両方成功。 |
| [03-03-infer-take-continuation.ref](cases/03-03-infer-take-continuation.ref) / [03-04-explicit-take-continuation.ref](cases/03-04-explicit-take-continuation.ref) | `e: _` を固定し、`step` の注釈を `_` / `A -> P` にする。 | 両方成功。 |
| [03-03-infer-take-continuation.ref](cases/03-03-infer-take-continuation.ref) / [03-05-explicit-witness.ref](cases/03-05-explicit-witness.ref) | `step: _` を固定し、`e` の注釈を `_` / `\exists A` にする。 | 両方成功。 |
| [03-05-explicit-witness.ref](cases/03-05-explicit-witness.ref) / [03-06-explicit-take.ref](cases/03-06-explicit-take.ref) | `e: \exists A` を固定し、`step` の注釈を `_` / `A -> P` にする。 | 両方成功。 |
| [03-04-explicit-take-continuation.ref](cases/03-04-explicit-take-continuation.ref) / [03-06-explicit-take.ref](cases/03-06-explicit-take.ref) | `step: A -> P` を固定し、`e` の注釈を `_` / `\exists A` にする。 | 両方成功。 |
| [03-07-infer-subset.ref](cases/03-07-infer-subset.ref) / [03-08-explicit-subset.ref](cases/03-08-explicit-subset.ref) | 部分集合の元 `x` の注釈を `_` / `Sub` にする。 | 両方成功。 |

存在消去の4ファイルは同じ宣言型と本体を持ち、証人と継続の注釈を独立に切り替える。
部分集合の比較では、元を台集合の関数 `f` に渡した後、`bysub` で所属の証明を取り出す。

<a id="g04"></a>

## G04: 定義した型名からの帰納型の操作

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [04-01-alias-constructor.ref](cases/04-01-alias-constructor.ref) / [04-02-direct-constructor.ref](cases/04-02-direct-constructor.ref) | constructor の参照を `Values::nil` / `List[A]::nil` にする。 | 両方成功。 |
| [04-03-alias-induction.ref](cases/04-03-alias-induction.ref) / [04-04-direct-induction.ref](cases/04-04-direct-induction.ref) | 帰納法の変数の型を `Values` / `List[A]` にする。 | 両方成功。 |

帰納型は parameter と constructor を1つずつ持つ型まで縮めた。
帰納法の比較では結果型と枝を固定し、対象の型名だけを変える。

<a id="g05"></a>

## G05: モジュール引数に依存する部分集合型の商

対応済み。以下は修正前の比較結果である。

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [05-01-dependent-type-minimal.ref](cases/05-01-dependent-type-minimal.ref) / [05-02-independent-type.ref](cases/05-02-independent-type.ref) | `Representation` の条件を `x = u` / `x = x` にする。 | 前者は失敗、後者は成功。 |
| [05-03-dependent-quotient.ref](cases/05-03-dependent-quotient.ref) / [05-04-independent-quotient.ref](cases/05-04-independent-quotient.ref) | `Representation` の条件を `x = interval` / `x = x` にする。 | 前者は失敗、後者は成功。 |
| [05-01-dependent-type-minimal.ref](cases/05-01-dependent-type-minimal.ref) / [05-05-forward-context.ref](cases/05-05-forward-context.ref) | `Pass` に未使用の引数 `u: Unit` を追加して `u := u` を渡す。 | 前者は失敗、後者は成功。 |

最初の2組の差分は部分集合の条件の右辺だけである。
外側のモジュールの具体化、内部 import、具体化後の関数呼び出しは共通である。
失敗時は `definition body check failed: types are not convertible` と診断され、具体化済みの `Representation` と具体化前の定義への参照が残る型が比較される。
最初の組は商を恒等関数に縮めても同じ不一致が生じることを確認し、次の組は代表元・同値類・商の台集合を残して比較する。

<a id="g06"></a>

## G06: 具体化したモジュール内の型と座標空間

対応済み。以下は修正前の比較結果である。

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [06-01-inner-inductive-minimal.ref](cases/06-01-inner-inductive-minimal.ref) / [06-03-direct-identity.ref](cases/06-03-direct-identity.ref) | 恒等関数の本体を `P.identity x` / `x` にする。 | 前者は失敗、後者は成功。 |
| [06-01-inner-inductive-minimal.ref](cases/06-01-inner-inductive-minimal.ref) / [06-02-outer-inductive.ref](cases/06-02-outer-inductive.ref) | `Unit` の宣言を parameter のあるモジュールの内部 / 外部に置く。 | 前者は失敗、後者は成功。 |
| [06-01-inner-inductive-minimal.ref](cases/06-01-inner-inductive-minimal.ref) / [06-04-forward-context.ref](cases/06-04-forward-context.ref) | `Pass` に未使用の引数 `K: \Set` を追加して `K := K` を渡す。 | 前者は失敗、後者は成功。 |

最初の組は1つの式だけを変え、内部 import を経由することの影響を確認する。
次の組は宣言を移し、利用側の型参照を `O.Unit` から `Unit` に合わせる。
いずれも同じ外側の parameter を具体化し、同じ恒等関数を利用する。
失敗時の診断は `definition body check failed: types are not convertible` で、具体化した `Outer.Unit` と元の `Outer.Unit` が一致しない。
体・基底の構成を恒等関数まで縮めた比較である。

<a id="g07"></a>

## G07: 圏の signature を添字に取る Set の構造

対応済み。以下は修正前の比較結果である。

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [07-01-signature-index-minimal.ref](cases/07-01-signature-index-minimal.ref) | 実引数は `Holder[C]`。 | 失敗：`Failed to access item at path`。 |
| [07-02-flattened-argument.ref](cases/07-02-flattened-argument.ref) | 実引数は `Holder[C.A]`。 | 成功。 |

圏の signature を Set のフィールド1つまで縮め、同じ `Holder` の宣言を使う。
添字の実引数だけを変えるので、宣言側と利用側で signature の展開がそろうかを比較できる。

<a id="g08"></a>

## G08: contextual な定義をモジュール引数に渡す

対応済み。以下は修正前の比較結果である。

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [08-01-contextual-argument.ref](cases/08-01-contextual-argument.ref) / [08-02-explicit-argument.ref](cases/08-02-explicit-argument.ref) | `identity` の lambda 注釈を `_` / `C.A` にする。 | 前者は失敗、後者は成功。 |
| [08-01-contextual-argument.ref](cases/08-01-contextual-argument.ref) / [08-03-bound-argument.ref](cases/08-03-bound-argument.ref) | `identity C` を直接渡す / 型注釈付きの `bound` を定義してその名前を渡す。 | 前者は失敗、後者は成功。 |

signature を取る contextual な恒等関数まで縮め、入力の型と渡す関数をそろえている。
最初の組の差分は lambda の注釈だけである。
次の組では元の `_` を維持し、定義を検査してから名前を渡すことの影響を確認する。
失敗時の診断は `module arguments do not allow inference holes` である。

<a id="g09"></a>

## G09: ブロックで導入した contextual な関手の射影

対応済み。以下は修正前の比較結果である。

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [09-01-block-minimal.ref](cases/09-01-block-minimal.ref) / [09-02-block-hash-projection.ref](cases/09-02-block-hash-projection.ref) | 射影を `x.field` / `x #field` にする。 | 前者は失敗、後者は成功。 |
| [09-01-block-minimal.ref](cases/09-01-block-minimal.ref) / [09-03-lambda-outside.ref](cases/09-03-lambda-outside.ref) | `x` を導入する lambda をブロックの内部 / 外部に置く。 | 前者は失敗、後者は成功。 |
| [09-04-block-let.ref](cases/09-04-block-let.ref) / [09-05-block-let-hash.ref](cases/09-05-block-let-hash.ref) | ブロックの `\let` で導入した `y` の射影を `y.field` / `y #field` にする。 | 前者は失敗、後者は成功。 |

関手をフィールド1つの record に縮め、同じ型の同じフィールドを取り出す。
次の組でも `x.field` を維持するので、射影の記法と束縛の位置を別々に比較できる。
失敗時の診断は `Module import 'x' was not found` である。

<a id="g10"></a>

## G10: 集合値関手の内部で具体化した自然変換の型

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [10-01-nested-transformation.ref](cases/10-01-nested-transformation.ref) | `Yoneda` の引数型を内部 import の `Maps.Transformation` から取得する。 | 成功。 |
| [10-02-local-transformation.ref](cases/10-02-local-transformation.ref) | 同じ `Family`・`Naturality`・`Transformation` を `Yoneda` 内で定義し、引数型にする。 | 成功。 |

対象集合、射、自然性、`fromElement`、具体化後の `evaluateFromElement` の等式は共通で、自然変換型を取得する場所だけを変える。
射を対象集合上の自己関数、合成を関数合成とする圏の表現可能関手に限定し、自然性と評価の等式を検査する。
他の修正に伴って解消済みとして扱う。
解消した変更は特定していないが、元の `Unit` と `C.Object` の不一致は再現しない。

<a id="g11"></a>

## G11: Machine の実行を Box にする定義

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [11-01-box-machine.ref](cases/11-01-box-machine.ref) | `machine` は定義の引数。 | 失敗：`Box requires a closed computation type`。 |
| [11-02-box-concrete.ref](cases/11-02-box-concrete.ref) | `machine` は既に定義した具体値。 | 成功。 |

差分は `runBox` の `(machine: Machine)` の有無だけである。
Machine の型、実行、Box の型と本体は共通で、Box の型は両側とも明示する。
入力と出力の型は1つの `State` にそろえている。
開いた computation type と、具体化して閉じた computation type の比較になる。
[Box の parameter の検討](../box-parameters.md#g11)に対応する。

<a id="g12"></a>

## G12: 帰納型の再帰的な述語

| 比較 | 共通の結果型 | 結果 |
| --- | --- | --- |
| [12-01-predicate-family.ref](cases/12-01-predicate-family.ref) / [12-02-predicate-family-constant.ref](cases/12-02-predicate-family-constant.ref) | `Nat -> Nat -> \Prop`。 | 両方成功。 |
| [12-03-predicate-induction.ref](cases/12-03-predicate-induction.ref) / [12-04-predicate-constant.ref](cases/12-04-predicate-constant.ref) | `Nat -> \Prop`。 | 両方成功。 |
| [12-05-predicate-powerset.ref](cases/12-05-predicate-powerset.ref) / [12-06-powerset-constant.ref](cases/12-06-powerset-constant.ref) | `Nat -> \Pow Nat`。 | 両方成功。 |

各組は同じ述語を、`induction` による再帰 / 非再帰の定数関数として定義する。
帰納型・宣言型・後続の `computes` は共通で、定義本体だけを変える。
`computes` は `succ zero` に対する同じ命題を `refl` で検査し、再帰を含む定義が実際に簡約されることも確認する。

<a id="g13"></a>

## G13: parameter を持つ帰納型の match

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [13-01-parameterized-match.ref](cases/13-01-parameterized-match.ref) | `List` 自身に要素型の parameter を持たせる。 | 成功。 |
| [13-02-monomorphic-match.ref](cases/13-02-monomorphic-match.ref) | モジュールの同じ要素型を使い、`List` 自身の parameter をなくす。 | 成功。 |

差分は帰納型の parameter の宣言と、それに伴う引数型 `List[A]` / `List` だけである。
要素型・constructor・結果型 `Bool`・match の枝は共通で、型 parameter の有無を比較する。

<a id="g14"></a>

## G14: 引数付きの算術定義を一致性証明で使う

対応済み。
修正後は最小比較の全3ケースと、算術定義12個を宣言ヘッダ形式に変えた標準ライブラリ全体が成功する。
以下は修正前の比較結果である。

比較対象は [Basic.Def](../../libs/std/src/Data/Nat/Basic/Def.ref) の算術関数と、[Parity.ProgramProp](../../libs/std/src/Data/Nat/Parity/ProgramProp.ref) の一致性証明である。
`add`・`pred`・`isZero`・`sub`・`eqb`・`leb`・`ltb`・`mul`・`pow`・`choose`・`min`・`max` の本体を保ち、引数を宣言ヘッダに移すと `EvenProof.matches` で `occurs check failed` が発生した。
現在の lambda 形式では成功する。
2026-10-07 の再検査では、`isZero` だけを宣言ヘッダ形式に変えても同じ場所で失敗した。

| 比較 | 変える条件 | 結果 |
| --- | --- | --- |
| [14-01-contextual-inference.ref](cases/14-01-contextual-inference.ref) / [14-02-lambda-inference.ref](cases/14-02-lambda-inference.ref) | 恒等関数を `identity(n: A): A := n` / `identity: A -> A := \fun (n: A) => n` と定義する。 | 前者は `occurs check failed`、後者は成功。 |
| [14-01-contextual-inference.ref](cases/14-01-contextual-inference.ref) / [14-03-explicit-inference.ref](cases/14-03-explicit-inference.ref) | 合同則に渡す `\fun (f: _) => identity (f n)` の注釈を `_` / `End` にする。 | 前者は `occurs check failed`、後者は成功。 |

最小比較では `End` は `A -> A` で、算術・Program・import は使わない。
集合、恒等関数の本体、証明対象、合同則は共通である。
