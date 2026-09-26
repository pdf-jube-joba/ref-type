# Elaboration

`elaboration` は `front-syntax` の module 構文を受け取り、名前解決と型推論を行い、kernel に分類済みの宣言を渡す。
`front` が構築した検査対象ごとに `GlobalEnvironment` を作る。

| 場所 | 担当 |
| --- | --- |
| `macros.rs` | macro template の衛生的な束縛、定義環境の名前解決、展開 |
| `resolved.rs` | 解決済みの定義・帰納型・record の参照 |
| `elaborator/` | module scope、宣言と項の elaboration、型に応じた構文の解釈 |
| `elaborator/analysis.rs` | 型・名前参照・出力を保持する semantic observations |
| `metavariables.rs` | 宣言単位の metavariable、constraint、goal |
| `raw/` | 未分類の項、環境、代入、型推論、評価 |
| `lowering/` | 解決済み raw IR から kernel 構文への変換と登録 |

macro 展開後も `\block` と `\induction` は構文として保持し、elaboration で期待される型を使って解釈する。
macro template の自由な名前は定義時の scope に解決し、module のインスタンス化に合わせて remap する。
source からの名前参照と associated access は span を保持する。

`MetaStore` は各宣言の終了時に clear し、goal と diagnostics に必要な情報は先に取り出す。
semantic observations は表示済みの型と source location を保持し、`front` が永続化する結果へ変換する。
raw と kernel の arena は検査する module 群の処理中に所有する。

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

`GlobalEnvironment` の `arena`、`crate_env`、`kernel_env` からノード数とキャッシュ件数を調べられる。
`REF_TYPE_PROFILE_DECLARATIONS` で宣言ごとの処理時間を表示できる。
