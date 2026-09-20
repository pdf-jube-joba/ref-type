# front の構成

front は未分類の構文を解析・elaboration し、kernel に渡す分類済み構文を作る。
最終的な型検査と定義の登録は kernel が行う。

| 場所 | 担当 |
| --- | --- |
| `parse/`・`parse.rs`・`syntax.rs` | 字句解析、構文解析、表面構文 |
| `module_loader.rs` | 外部ファイルを含む module の読み込み |
| `macros.rs` | マクロの展開と衛生的な名前解決 |
| `elaborator/`・`metavariables.rs` | 宣言・項の elaboration、文脈、名前空間、制約の解決 |
| `raw/` | elaboration 中の未分類構文、環境、構造操作、評価 |
| `lowering/` | 解決済みの raw 構文から kernel 構文への変換と登録 |

## 構造操作

論理側と Program 側をまたぐ束縛の深さは [`raw/traversal.rs`](src/raw/traversal.rs)
に集約する。
走査に渡すクロージャが部分木の置換を返した場合、その部分木の走査を止める。
変更がないノードは元の handle を使う。
シフト・telescope 代入・module parameter 置換は、ノードと束縛の深さをキーに走査結果を共有する。
自由な de Bruijn index の最大値をノードごとに保存し、シフトや代入が影響しない部分木の走査を省く。
変数・帰納型の出現判定も共有部分木を一度ずつ調べる。

論理ノードと自由変数の情報は固定長のチャンクに格納し、arena の拡張時に全体をコピーする費用と余剰容量を抑える。
型推論と lowering のキャッシュは、局所文脈の型の列を接頭辞ごとに共有した ID で参照する。
`CheckSession` は binder の出入りに合わせてこの ID を更新する。
raw の名前参照は解決済みの ID なので、型推論のキーは式と文脈の ID になる。

- [`raw/program_definitions.rs`](src/raw/program_definitions.rs) は定義の型引数を同時代入する。
  単一の型引数を代入する入口もこの実装を使う。定義代入は評価時にも呼ばれるため、
  性能比較で遅くなった汎用走査への置き換えは採用せず、専用処理を保つ。
- `raw/calculus.rs` と `raw/program_calculus.rs` は ID 置換、比較、簡約・評価を提供する。
- 論理側の弱頭簡約は `CrateEnv` 内で結果を再利用する。raw ノードと登録済み宣言は
  不変で、この簡約は局所文脈や metavariable の解決状態に依存しない。
  refinement の消去はキャッシュした通常の簡約の後に行い、厳密な比較と区別する。
  連続した lambda への適用は引数をまとめて同時代入し、部分適用の中間ノードの生成を抑える。
- `raw/reflection.rs` は Program を論理構文へ反映する。型の反映は定義を展開しないため
  巡回検出の状態を持たず、定義を辿る値・計算の反映でのみ巡回を検出する。

未解決の Program type の metavariable spine をそのまま保持するという既存の方針は、
定義代入と ID 置換の各処理で保つ。評価では計算位置と証明の扱いを各評価規則に従って決める。

## kernel 構文の構築

適用・product・lambda・帰納型の構築には `kernel::construction` を使う。
その他の論理構文は [`lowering/nodes.rs`](src/lowering/nodes.rs) の `logical_node!` により、
許可する family と構築するフィールドを [`lowering/logical.rs`](src/lowering/logical.rs)
に一度だけ記述する。各 family のフィールド型は Rust が検査する。
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
env -u RUST_LOG /usr/bin/time -f 'elapsed=%e user=%U sys=%S maxrss_kb=%M' target/release/cli lib/root.ref
```

`--stats` を付けると、処理後に raw と kernel の family ごとの保持ノード数を標準エラーへ表示する。
推論・弱頭簡約のキャッシュ件数、文脈の束縛数、kernel の宣言から到達できるノード数も表示する。
文脈の束縛数は raw では共有された文脈の拡張数、kernel ではキャッシュ内の文脈の長さの合計である。
宣言からの到達数には、キャッシュと外部の handle だけが保持するノードは含まない。
これらは `Arena::node_counts`、`Environment::cache_counts`、`CrateEnv::cache_counts`、`Environment::declaration_node_count` からも取得できる。
