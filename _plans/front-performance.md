# front の elaboration・lowering・raw 演算を高速化する

## 対象

`src/front` の読み込みから kernel 登録までと、raw 構文の正規化・評価を計測する。メタ変数の重複走査、context のコピー、lowering の再分類と列挙を中心に調べ、実測した寄与に応じて改善する。

[kernel の性能計画](kernel-performance.md)とは計測結果を分ける。instance の対応表・名前空間・resolver の改善は[モジュール実体化の計画](lazy-module-instantiation.md)で扱い、本計画では共通の測定方法と lowering の処理対象を整える。

| 箇所 | 現在の処理 | 改善候補 |
| --- | --- | --- |
| `MetaStore::contains_unsolved` | 各再帰段で `zonk` し、子でも繰り返す。`zonk` のキャッシュは呼び出し内に限られる | 展開と未解決判定の作業領域を共有する |
| `MetaStore::unify_rec` / `finish` | 比較の各再帰段や assignment の終了確認で `zonk`・未解決判定を繰り返す | 同じ代入状態で訪問結果を再利用する |
| raw `CheckSession` の推論 | `(式, context の (名前, 型) 列, ModuleId)` を毎回構築する | context の共有と ID によるキー生成 |
| `GlobalEnvironment::infer` / `fresh_meta` | module context と local context を結合し、メタ変数には context を保存する | 共通 prefix の共有 |
| `Lowerer::set` / `context` | context の型列をキーに raw 推論・formation・WHNF で分類し、context 変換は prefix を辿る | 分類と context 変換の再利用 |
| `Lowerer::new` / `lower_all` | 式キャッシュは Lowerer ごとに作る。宣言 ID の取得時には全スロットを走査し、初期化済みだけを返す | 式キャッシュの寿命と処理対象の追跡 |
| raw arena・演算 | 読み取りの clone、変換時の再構築、正規化・比較・評価の走査を行う | 残る確保と重複走査の削減 |

参照: [metavariables.rs](../src/front/src/metavariables.rs)、[elaborator.rs](../src/front/src/elaborator.rs)、[raw/derivation.rs](../src/front/src/raw/derivation.rs)、[lowering.rs](../src/front/src/lowering.rs)、[lowering/logical.rs](../src/front/src/lowering/logical.rs)、[lowering/declarations.rs](../src/front/src/lowering/declarations.rs)。

## 1. 段階別の計測を追加する

[既存ハーネス](../src/cli/benches/performance.rs)の `parse/mccarthy91`、`load/library`、`check/library`、`pipeline/*`、`instantiate/128x16-*`、`normalize/beta256`、`evaluate/countdown*` を基準にする。

`check/library` には elaboration・lowering・kernel 検査が含まれる。`instantiate/128x16-*` も元モジュールを含む elaboration を測っているため、次の内訳を診断実行で取得する。

1. 読み込み・構文解析。
2. マクロ展開・名前解決・インスタンス作成と項の実体化。
3. raw 項の構築・推論・メタ変数の解決と終了確認。
4. raw から kernel への分類・変換と依存宣言の準備。
5. kernel の検査・登録。
6. 評価コマンドの評価。

包括時間と子の処理を除いた時間を区別する。時間計測は tracing subscriber なしで行い、割り当て量・訪問数・キャッシュの利用状況は別に調べる。

| 追加ケース群 | 比較する負荷 |
| --- | --- |
| `front/meta/*` | メタ変数のない深い式、共有部分、解決済みメタ変数の連鎖、未解決・矛盾・スコープ制約 |
| `front/infer/*` | 浅い／深い context、同じ型の反復、Set/Prop と多相 Program |
| `front/lowering/*` | 型演算子、共有型、大きな context、反映証明、複数 root module の逐次追加 |
| `front/raw/*` | 開いた式の代入、共有部分の比較、深い適用・Sequence の評価 |
| `front/parse/*` / `front/macro/*` | 大きな宣言列、深い構文、マクロの反復利用、大きな capture |

instance の追加ケースは既存の `instantiate/` 群を拡張する。private な処理には限定的な計測用入口を使い、Lowerer・MetaStore の通常の公開範囲を広げない。

入力サイズを複数用意し、準備と結果検証を計測外に置く。反復ごとに新しい環境を使い、キャッシュ再利用・逐次追加は反復内のシナリオにする。時間・ばらつき・割り当て量・保持量に加え、`zonk` 訪問数、context キー生成量、raw/kernel ノード数、宣言の走査スロット数・変換数・検査数を記録する。

## 2. メタ変数の重複走査を減らす

`contains_unsolved` の問い合わせ全体で展開・訪問の作業領域を共有する。最初に zonk した結果を一度走査する方式と、展開しながら未解決を判定する方式を比較する。

- `finish` は代入状態を変更しないため、複数 assignment の確認に作業領域を再利用する。
- `unify_rec` では代入が起きたときに結果を無効化する。世代番号は無効化の管理費を測ってから判断する。
- 同名メタ変数の共通スコープ変更、assignment の rebasing、clear、試行的検査の復元を扱う。ID が再利用される状態へ古い結果を持ち越さない。
- occurs check、spine による代入、変数捕捉の拒否、goal と制約の診断を維持する。

深い式・共有された式で訪問数を減らし、解決結果・拒否結果・エラー位置と goal の context を保つ。

## 3. context と raw 推論キャッシュを改善する

raw の context を `(親ContextId, entry)` で共有し、Set/Prop 推論キーを `(Exp, ContextId, ModuleId)` にする。entry にある名前と型の区別を維持し、kernel の context ID とは別に管理する。

- session の push/pop を ID と同期し、module prefix と local context の結合を共有する。
- 外部からの context 変更を公開入口で反映する。
- メタ変数の保存 context は診断・スコープ計算にも使うため、binder 名・順序・局所 scope の境界を保持する。
- 宣言や checking scope の更新に伴う推論キャッシュ無効化を維持する。
- Program 推論の再実行が主要コストなら、value/type binder と全依存情報を区別した成功結果のキャッシュを比較する。

深い context で確保を減らし、異なる module・context の結果を混同しないことを確認する。浅い context の管理費も測る。

## 4. lowering の再分類とスロット走査を減らす

`definition_ids`・`inductive_ids`・`datatype_ids` は `OnceCell` が初期化済みの宣言だけを返すが、その判定には全モジュールのスロットを辿る。`lower_all` が受け取った通常の定義とテンプレートは、kernel に登録されていれば検査を省略する。走査・分類・変換・検査を別々に測る。

- `Lowerer::set` のキーを context ID にし、同じ prefix の kernel context への変換も再利用する。
- raw 推論・formation・WHNF の再利用範囲を確認する。メタ変数の解決前に得た分類を確定情報として保存しない。
- module 追加や query をまたぐ再変換が大きければ、式キャッシュを `GlobalEnvironment` の寿命に合わせる。raw/kernel 環境の対応、module・context、環境更新をキーと無効化に反映する。
- スロット走査が主要コストなら、元宣言の追加と lazy slot の実体化成功を処理対象のキューに記録する。lowering 中に新しく要求された依存先も処理する。
- 元宣言は未使用でも検査し、未実体化の instance 項はキューへの列挙だけで要求しない。
- 依存探索中の状態と検査成功を分離し、kernel の独立検査、反映・positivity・閉性の検査を維持する。

複数 module・繰り返し query で不要な列挙や再分類を減らし、依存先の登録と循環の拒否を保つ。

## 5. raw 演算と構文処理の候補

計測で寄与が大きいものを選ぶ。

- **raw ノードのコピー。** Program の borrow/reuse API を起点に、読み取りと変更のない変換の確保を減らす。同じ partition への割り当て前に borrow を解放する。共有化や interning は保持量・ハッシュの費用も比較する。
- **比較・代入・評価。** 正規化のメモ化と比較内 WHNF キャッシュを前提に、ペア比較・代入の再走査と評価位置の再探索を測る。環境・メタ変数・erasure の違いを区別し、Program の評価順序・fuel・反映証明を維持する。
- **Program の構文分類。** `SExp` clone、型分類の試行、型メタ変数の zonk と型頭部の解決を測る。変更しない型の再構築を避ける処理も含めて確認する。
- **マクロ。** 初回の `macro_scope` 取得で source scope 全体を clone・remap し、展開時にも template を clone して binder を更新する。一つだけ使う大きな scope と反復展開を測り、項目ごとの変換・不変 template の共有を比較する。hygiene、宣言順、module scope、fresh な binder、source span を保つ。
- **読み込み・構文解析。** AST・token のコピーとパス構築を調べる。source 本文の `Arc` 共有、ファイル重複使用の拒否、エラー位置を維持する。OS キャッシュが温まった測定条件を記録する。

## 検証と記録

実装段階ごとに `cargo test --workspace` を実行する。回帰テストは、context の共有、メタ変数の代入・スコープ変更・試行失敗、宣言更新、遅延実体化、Program 多相型と反映証明など、変更が影響する境界に絞る。

推論した型・kernel 登録・評価結果を比較し、不正な未使用宣言や引数の拒否、source location、goal の context と制約の状態を維持する。

対象ケースと `check/library`・`pipeline/library` の時間・ばらつき・確保量・保持量を記録する。kernel を固定して front の効果を比較し、再現性のある改善を採用する。
