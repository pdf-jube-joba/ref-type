# gaps の最小比較サンプル

各 `.ref` の全文を playground.md に貼り付けて、1ファイルずつ検査する。
必要な宣言は各ファイルに含まれ、標準ライブラリや外部ファイルの import は不要である。
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
| [G11](#g11) | Machine の引数と具体値 | 引数で失敗、具体値で成功。 |

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
