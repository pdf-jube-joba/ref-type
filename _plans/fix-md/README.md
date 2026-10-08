# gaps の最小比較サンプル

G01〜G05 と G11 の `.ref` は、全文を playground.md に貼り付けて、1ファイルずつ検査する。
G01〜G05 と G11 では、必要な宣言は各ファイルに含まれ、標準ライブラリや外部ファイルの import は不要である。
G06 は外部ライブラリを具体化するため、別のプロジェクトとして検査する。
`\root.Repro[]` への参照は、同じファイル内のモジュールを具体化する。
比較する組では、下記の条件だけを変え、それ以外の宣言・入力・検査対象をそろえている。

個別に CLI で確認する場合は、リポジトリのルートで実行する。

```sh
cargo build --locked --offline -p cli
target/debug/cli _plans/fix-md/cases/01-01-record-eta.ref --no-cache --diagnostics compact
```

<a id="対象文書の対応"></a>

## 項目と比較対象

| 項目 | 変える条件 | 結果 |
| --- | --- | --- |
| [G01](#g01) | record の変数と具体値 | 変数で失敗、具体値で成功。 |
| [G02](#g02) | 通常の関数と contextual な定義 | 通常の関数で失敗、contextual な定義で成功。 |
| [G03](#g03) | 関係を持つ record とデータ・法則の分離 | record の射影生成で失敗、分離すると成功。 |
| [G04](#g04) | 親の macro 読み込み位置と子の再読み込み | 宣言後の読み込みと再読み込みで失敗、宣言前の読み込みを継承すると成功。 |
| [G05](#g05) | 式中の module 具体化と台集合を返す関数 | 式中の具体化・関数とも成功。 |
| [G06](#g06) | 積の定理の定義元と parameter を持つ利用側 | 修正済み。両方成功。 |
| [G11](#g11) | Machine の引数と具体値 | 引数で失敗、具体値で成功。 |
| [G16](#g16) | 構造を返す関数と名前付きの添字付き module | 関数のフィールドで添字が残り失敗、module の具体化で成功。 |

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

## G03: 関係を parameter に持つ record

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [03-01-relation-record.ref](cases/03-01-relation-record.ref) | `Selection[relation]: \Set` に値と法則を保持する。 | 失敗：`Generated projection value does not typecheck: no product rule for these sorts`。 |
| [03-02-relation-record-split.ref](cases/03-02-relation-record-split.ref) | データと法則を分け、部分集合型で結ぶ。 | 成功。 |

保持する値と条件は共通で、record に関係 parameter を渡すか、法則を満たすデータの部分集合型を使うかを比較する。

<a id="g04"></a>

## G04: macro の読み込みと継承

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [04-01-macro-late.ref](cases/04-01-macro-late.ref) | 親の `\use` は子の宣言より後。 | 失敗：`Named macro 'reflexive' is not visible`。 |
| [04-02-macro-early.ref](cases/04-02-macro-early.ref) | 親の `\use` は子の宣言より前。 | 成功。 |
| [04-03-macro-duplicate.ref](cases/04-03-macro-duplicate.ref) | 子で同じ macro を再び `\use` する。 | 失敗：`Macro 'reflexive' is already visible`。 |
| [04-04-macro-inherited.ref](cases/04-04-macro-inherited.ref) | 子で継承された macro を利用する。 | 成功。 |

最初の組は親の `\use` の位置だけを変え、次の組は子の `\use` の有無だけを変えている。
macro の定義、引数、子で検査する等式は共通である。

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

<a id="g05"></a>

## G05: 式の中での module の具体化

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [05-01-module-expression.ref](cases/05-01-module-expression.ref) | 引数を module の具体化へ渡して台集合を参照する。 | 成功。 |
| [05-02-carrier-function.ref](cases/05-02-carrier-function.ref) | 台集合を返す通常の関数へ引数を渡す。 | 成功。 |

両方とも引数の集合をそのまま返す型族を定義する。
前者は module 参照、後者は関数適用で表現する。

<a id="g06"></a>

## G06: 積のコンパクト性定理の具体化

[再現プロジェクト](../reproductions/g06-product-compactness/ref.toml) は、`topology` に依存し、同じ命題を持つ定理に `Product.Compactness.productCompact` と `productCompactIn` を適用する。
[診断と実行方法](../gaps.md#g06) に、修正前の診断と、修正後に両方成功する定義元・利用側の検査を記載する。
単独ファイルへ貼り付ける形式ではない。

<a id="g16"></a>

## G16: 構造の依存するフィールド

| サンプル | 条件 | 結果 |
| --- | --- | --- |
| [function-result.ref](../reproductions/g16-structure-family/function-result.ref) | `bundle(i)` から型族のフィールドを返し、`bundle j` で参照する。 | 失敗：期待型に宣言元の `i` が残る。 |
| [named-piece.ref](../reproductions/g16-structure-family/named-piece.ref) | `At[i := j]` を名前付き import で固定し、フィールドを参照する。 | 成功。 |

型族と返す構造は共通で、別の添字での参照方法を比較する。
[診断と実装上の回避](../gaps.md#g16) に、貼り合わせでの利用を記載する。
