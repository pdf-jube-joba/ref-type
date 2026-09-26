# Elaboration

`elaboration::Checker` は `resolve::Project` の HIR を受け取り、型推論と kernel による検証を行う。
`sema` は対象の module 群を名前解決した後、この API に渡す。

| 場所 | 担当 |
| --- | --- |
| `api.rs` | HIR を受け取る検査 API、arena から独立した診断・goal・統計 |
| `items.rs` | 型検査済みの定義・帰納型・record の内部参照 |
| `elaborator/` | HIR の ID と workspace の対応、型推論、型に応じた構文の解釈 |
| `elaborator/analysis.rs` | 型・名前参照・出力を保持する semantic observations |
| `metavariables.rs` | 宣言単位の metavariable、constraint、goal |
| `raw/` | 内部の項・環境・代入・型推論・評価 |
| `lowering/` | 解決済み raw IR から kernel 構文への変換と登録 |

公開する中間表現は `syntax` の AST、`resolve` の型推論前の HIR、`kernel` の分類済みの項である。
raw IR と metavariable は elaboration の内部実装として扱う。

HIR の束縛 ID から対応する宣言やローカル変数を取得し、module 引数の型検査と具体化、型に依存する field 選択を行う。
HIR の `\block` と `\induction` は期待される型を使って解釈する。
各 `Checker::check` は新しい workspace を構築し、同じ HIR を繰り返し検査できる。

`MetaStore` は各宣言の終了時に clear し、goal と diagnostics に必要な情報は先に取り出す。
`Diagnostic` と `Goal` は文脈・判断・制約の表示と source location を保持する。
`analysis` は表示済みの型・宣言・参照・query 出力を持ち、`sema` が永続化する結果へ変換する。

## 構造操作

論理側と Program 側をまたぐ束縛の深さは `raw/traversal.rs` に集約する。
変更がない部分木では元の handle を使い、シフト・代入・ID 置換は共有部分木ごとに結果を再利用する。
ノードに記録した自由変数の最大値を使って、操作の影響がない部分木を省く。

型推論と lowering は局所文脈の接頭辞を共有した ID をキャッシュのキーに使う。
論理側の弱頭簡約は `CrateEnv` で再利用し、連続する lambda への適用では引数をまとめて代入する。
Program の型引数の代入は `raw/program_definitions.rs` にまとめる。

## Kernel への接続

適用・product・lambda・帰納型の構築には `kernel::construction` を使う。
その他の論理ノードは `lowering/nodes.rs` と `lowering/logical.rs` に family ごとの構築規則を記述する。
構築した項と宣言は kernel の独立した型検査・登録を通す。

`Checker::statistics` からノード数・キャッシュ件数・具体化件数を取得できる。
`Checker::kernel_environment` から kernel の検証済み環境と診断 API を利用できる。
`REF_TYPE_PROFILE_DECLARATIONS` で宣言ごとの処理時間を表示できる。
