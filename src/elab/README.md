# Elaboration の構成

elab は HIR から推論用の項を構築し、metavariable と制約を解決して kernel に渡す分類済み構文を作る。
最終的な型検査と定義の登録は kernel が行う。

| 場所 | 担当 |
| --- | --- |
| `../syntax/src/` | source の AST、位置、字句解析、構文解析 |
| `../hir/src/` | 展開用の構文、proof block、scope と capture の参照、AST からの変換と走査 |
| `../sema/src/elaborator/` | 宣言の処理順、module の特殊化、名前解決、参照の記録 |
| `../sema/src/macros.rs` | macro の環境、展開、衛生的な名前の束縛、capture の保持 |
| `src/term_elaborator.rs`・`src/program_term_elaborator.rs` | 論理項と Program 項の elaboration、局所文脈 |
| `src/metavariables.rs` | 論理項の metavariable、制約、unification、zonk |
| `src/exp.rs`・`src/program.rs` | 推論用の項と arena |
| `src/environment.rs` | 推論・簡約・特殊化に使う宣言と作業 cache |
| `src/lowering/` | kernel 構文への変換と登録 |

`Handler` trait は名前・member の解決、macro 展開、参照の記録を sema に委ねる。
論理項と Program 項の elaborator はそれぞれこの interface を使い、型依存の処理を進める。
HIR は検査する宣言と module parameter ごとに AST から作り、処理後に解放する。
後続の宣言が使う macro template は sema が保持する。
HIR の `ScopeId` と `CapturedId` は、その HIR を処理する semantic 環境が解釈する。
macro が捕捉した module parameter の項は sema の capture table に保存し、特殊化時に代入した項へ新しい ID を割り当てる。
宣言境界では公開された宣言、macro、query output の到達可能部分を保持し、作業ノードと推論 cache を回収する。

## 構造操作

論理側と Program 側をまたぐ束縛の深さは [traversal.rs](src/traversal.rs) に集約する。
走査に渡すクロージャが部分木の置換を返した場合、その部分木の走査を止める。
変更がないノードは元の handle を使う。
シフト・telescope 代入・module parameter 置換は、ノードと束縛の深さをキーに走査結果を共有する。
自由な de Bruijn index の最大値をノードごとに保存し、シフトや代入が影響しない部分木の走査を省く。
変数・帰納型の出現判定も共有部分木を一度ずつ調べる。

論理ノードと自由変数の情報は固定長のチャンクに格納し、arena の拡張時に全体をコピーする費用と余剰容量を抑える。
型推論と lowering のキャッシュは、局所文脈の型の列を接頭辞ごとに共有した ID で参照する。
`CheckSession` は binder の出入りに合わせてこの ID を更新する。
推論用の項の名前参照は解決済みの ID なので、型推論のキーは式と文脈の ID になる。

- [program_definitions.rs](src/program_definitions.rs) は定義の型引数を同時代入する。
  単一の型引数を代入する入口もこの実装を使う。
  評価時の定義代入には専用処理を使う。
- `calculus.rs` と `program_calculus.rs` は ID 置換、比較、簡約・評価を提供する。
- 論理側の弱頭簡約は `CrateEnv` 内で結果を再利用する。
  項と登録済み宣言は不変で、この簡約は局所文脈や metavariable の解決状態に依存しない。
  refinement の消去はキャッシュした通常の簡約の後に行い、厳密な比較と区別する。
  連続した lambda への適用は引数をまとめて同時代入し、部分適用の中間ノードの生成を抑える。
- `reflection.rs` は Program を論理構文へ反映する。
  型の反映は定義を展開しないため巡回検出の状態を持たず、定義を辿る値・計算の反映でのみ巡回を検出する。

未解決の Program type の metavariable spine は、定義代入と ID 置換の各処理で保持する。
評価では計算位置と証明の扱いを各評価規則に従って決める。

## kernel 構文の構築

適用・product・lambda・帰納型の構築には `kernel::construction` を使う。
その他の論理構文は [lowering/nodes.rs](src/lowering/nodes.rs) の `logical_node!` により、許可する family と構築するフィールドを [lowering/logical.rs](src/lowering/logical.rs) に一度だけ記述する。
各 family のフィールド型は Rust が検査する。
構築関数の呼び出し後も、kernel の独立した型検査・定義登録を通す。

## 検証

リポジトリのルートで実行する。

```sh
cargo test --workspace --locked --offline
cargo clippy --workspace --all-targets --locked --offline -- -D warnings
```

ライブラリ全体の処理時間と最大メモリ使用量は release ビルドで比較する。
ビルド時間を除き、他のビルドやテストが動いていない状態で複数回測る。

```sh
cargo build --release --locked --offline
env -u RUST_LOG /usr/bin/time -f 'elapsed=%e user=%U sys=%S maxrss_kb=%M' target/release/cli tests/library/ref.toml
```

`--stats` を付けると、処理後に推論用の項と kernel の family ごとの保持ノード数を標準エラーへ表示する。
表示中の `raw` は推論用の項を指す。
推論・弱頭簡約のキャッシュ件数、文脈の束縛数、kernel の宣言から到達できるノード数も表示する。
文脈の束縛数は elab では共有された文脈の拡張数、kernel ではキャッシュ内の文脈の長さの合計である。
宣言からの到達数には、キャッシュと外部の handle だけが保持するノードは含まない。
これらは `Arena::node_counts`、`Environment::cache_counts`、`CrateEnv::cache_counts`、`Environment::declaration_node_count` からも取得できる。
`REF_TYPE_PROFILE_DECLARATIONS` と `REF_TYPE_PROFILE_LOCAL_DEFINITIONS` は宣言と局所定義ごとの時間を表示する。
