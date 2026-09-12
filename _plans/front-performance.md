# front の elaboration・lowering・raw 演算を高速化する

## 目的と優先順位

`src/front` の読み込みから kernel への登録までの処理と、raw 構文上の正規化・評価を高速化する。最初に段階別の計測を追加し、メタ変数の重複走査、コンテキストのコピー、lowering の再分類・全体走査を順に調べる。raw ノードのコピーや評価、構文解析・マクロの改善は測定した寄与に応じて進める。

この文書は実装を読んだ段階の計画であり、ボトルネックと改善率は未計測。以下の順序は初期案とし、各段階の測定結果で変更する。

- [kernel の高速化計画](kernel-performance.md) は indexed 構文側の最適化を扱う。front 全体の測定には kernel の検査時間も含まれるため、両者の効果を分けて記録する。
- [モジュールの遅延インスタンス化計画](lazy-module-instantiation.md) は大きな独立作業として扱う。本計画では比較用の負荷と計測点を整え、詳細設計は既存計画を参照する。

## 現状と候補

| 箇所 | 確認した処理 | 改善候補 |
| --- | --- | --- |
| `MetaStore::contains_unsolved` | 各再帰段で `zonk` を呼び、子に対しても同じ処理を行う。`zonk` のキャッシュは一回の呼び出し内に限られる | 解決済みメタ変数の展開と未解決判定の走査を共有する |
| `MetaStore::unify_rec` / `finish` | 再帰的な比較や各メタ変数の終了確認で `zonk`・未解決判定を繰り返す | 同じ代入状態で作業領域を再利用する |
| raw `CheckSession::infer` | `(式, context の (名前, 型) 列, ModuleId)` を毎回構築して推論キャッシュを検索する | context を ID で共有し、キーの確保とハッシュを減らす |
| `GlobalEnvironment::infer` / `fresh_meta` | module context を取得し、local context と結合する。メタ変数の生成時には context を保存する | module prefix と local context の共通部分を共有する |
| `Lowerer::set` | context の型列を毎回キーにし、raw の型推論・formation・WHNF で構文を分類する | キー改善、分類結果と context 変換結果の再利用 |
| `Lowerer::new` / `lower_all` | Lowerer ごとに式キャッシュ・検査済みテンプレート集合を作る。root module 追加後に全宣言 ID を列挙する | キャッシュの寿命見直しと未処理宣言の追跡 |
| raw `Arena::get` / `alloc` | node の clone と新規追加が基本。Program 側には borrow と変更のない node の再利用 API がある | 読み取り時のコピーと同じ構造の再構築を減らす |
| raw 正規化・比較・評価 | 正規化内のメモ化と比較内の WHNF キャッシュがある | 残る走査・代入・コピーの寄与を調べる |

参照コード:

- [metavariables.rs](../src/front/src/metavariables.rs)
- [elaborator.rs](../src/front/src/elaborator.rs)
- [raw/derivation.rs](../src/front/src/raw/derivation.rs)・[raw/program_derivation.rs](../src/front/src/raw/program_derivation.rs)
- [lowering.rs](../src/front/src/lowering.rs)・[lowering/logical.rs](../src/front/src/lowering/logical.rs)・[lowering/declarations.rs](../src/front/src/lowering/declarations.rs)
- [raw/exp.rs](../src/front/src/raw/exp.rs)・[raw/calculus.rs](../src/front/src/raw/calculus.rs)・[raw/program_calculus.rs](../src/front/src/raw/program_calculus.rs)

## 1. 計測する処理を分ける

[既存ハーネス](../src/cli/benches/performance.rs) の `parse/mccarthy91`、`load/library`、`check/library`、`pipeline/*`、`normalize/beta256`、`evaluate/countdown*` を基準として保存する。最後の正規化・評価ケースは既に `front::raw` を測っているため、名前と入力を維持して比較に使う。

`check/library` は読み込み・構文解析を除外するが、elaboration・lowering・kernel 検査が混ざる。診断用の計測点で次の内訳を取る。

1. 読み込み・構文解析。
2. マクロ展開・名前解決・モジュール実体化。
3. raw 項の構築、推論、メタ変数の解決・終了確認。
4. raw から kernel への分類・変換と依存宣言の準備。
5. kernel の検査・登録。
6. 評価コマンドがある場合の評価。

これらは呼び出しが入れ子になるため、包括時間と子の処理を除いた時間を区別する。時間を単純に足して二重計上しない。通常のベンチは tracing subscriber なしを維持し、内訳や割り当ての計測は別の診断実行で行う。

追加するケースは `front/` 接頭辞で分類する。

| ケース群 | 比較する負荷 |
| --- | --- |
| `front/meta/*` | メタ変数を含まない深い式、共有部分の多い式、解決済みメタ変数の連鎖、未解決・矛盾・スコープ制約を含む入力 |
| `front/infer/*` | 浅い／深い context、同じ型の繰り返し、Set/Prop と多相 Program の推論 |
| `front/lowering/*` | 型演算子、共有型、大きな context、反映証明を持つ宣言、複数 root module の逐次追加 |
| `front/instantiate/*` | 大きな module を複数回インスタンス化し、一部／全部の項を使用。親・内部 import を持つ場合も測る |
| `front/raw/*` | 開いた式の代入、共有部分の比較、深い適用・Sequence の評価 |
| `front/parse/*` / `front/macro/*` | 大きな宣言列、深い構文、同じマクロの反復利用と大きな capture |

private な処理の測定は front 内のテスト用ハーネスや限定的な計測用入口を使う。ベンチのためだけに Lowerer・MetaStore を通常の公開 API にしない。準備済み raw 環境が必要な場合、kernel 検査を経ない経路を通常の利用者へ公開しない。

各ケースでサイズを複数用意し、時間・ばらつき・割り当て量・保持メモリを比較する。追加の指標は `zonk` 訪問数、context キーの生成量、raw/kernel のノード数、lowering の cache hit/miss、宣言の列挙数・変換数・検査数とする。

原則として反復ごとに新しい環境を作り、入力準備と結果検証は計測外に置く。キャッシュ再利用や逐次追加は反復内に明示的なシナリオを作る。失敗系は期待するエラーで失敗することも検証する。

## 2. メタ変数の重複走査を減らす

最初は `contains_unsolved` を対象にする。現状はある部分式を `zonk` した後、その各子でも新たに `zonk` するため、深い式で同じ部分を繰り返し訪問し得る。

- 一回の問い合わせ全体で展開・訪問の作業領域を共有する。最初に zonk した結果を一度だけ走査する方式と、展開しながら未解決を判定する方式を比較し、小さい変更から始める。
- `finish` は代入状態を変更しないので、複数の assignment の確認で作業領域を再利用する。共有部分を何度も走査しない。
- `unify_rec` 内で再利用する場合は、代入で状態が変わる点を扱う。初版は代入時に結果を無効化する方式とし、必要なら単調に増える世代番号を導入する。
- `fresh` による同名メタ変数の共通スコープ変更、assignment の rebasing、clear、試行的検査の復元など、結果に影響する変更を列挙する。メタ変数 ID が再利用される状態へ古い結果を持ち越さない。
- occurs check、spine による代入、共通 context 外への変数捕捉の拒否、未解決 goal と制約の診断を維持する。

完了条件は、深い式・共有された式で訪問数が減り、解決結果・拒否結果・エラー位置と goal の context が一致すること。永続的なキャッシュは、この作業領域の共有で残るコストを見てから判断する。

## 3. context と raw 推論キャッシュを改善する

- raw の context を `(親ContextId, entry)` で共有し、Set/Prop 推論キーを `(Exp, ContextId, ModuleId)` にする。現状の entry は名前と型を含むため、最初はその区別を維持する。
- kernel の ContextId と raw の ContextId は別物として管理する。raw handle を kernel のキーへ混ぜない。
- session の push/pop を ID と同期する。module context の取得・local context の結合は共通 prefix を再利用し、公開入口で外部からの context 変更を反映する。
- メタ変数の保存 context は診断とスコープ計算にも使われる。型だけに縮めず、binder 名・順序・局所 scope の境界を保持する。
- 環境の宣言・checking scope など、推論結果に影響する変更に対する既存のキャッシュ無効化を維持する。
- Program 推論の再実行が主要コストなら成功結果のキャッシュを追加する。value/type binder の種別と context の全依存情報をキーに含め、エラーや未確定の推論を再利用しない。

完了条件は、深い context でキー生成・結合の確保が減り、同じ式でも module・context が異なる場合に結果を混同しないこと。浅い context での管理費も測る。

## 4. lowering の再分類と全宣言走査を減らす

`lower_all` は全 ID を列挙するが、kernel に登録済みの通常の宣言は処理を省略する入口がある。「毎回すべてを再検査する」とは仮定せず、列挙・分類・変換・検査の各回数を分けて測る。

- `Lowerer::set` のキーを context ID にし、同じ context prefix の kernel context への変換も再利用する。
- 同じ項の分類に必要な raw 推論・formation・WHNF の再利用を確認する。elaboration で得た分類を運ぶ場合も、未解決メタ変数の解決前の結果を確定情報として使わない。
- まず一回の module 追加・query の範囲でキャッシュを活用する。その後も繰り返しが大きければ、式変換と `checked_templates` の成功結果を `GlobalEnvironment` が保持する状態へ移す。
- 永続化するキーには raw/kernel 環境の対応、module・context、分類に影響する環境変更を反映する。依存関係の探索中を表す active 集合と、成功済みの状態を分け、失敗を検査済みとして保存しない。
- root module の逐次追加時に全 ID を列挙する負担が大きければ、新規・更新宣言を追跡する。関連定義・反映で生成される宣言を含めて処理が尽きるまで追跡し、未使用の元宣言も従来どおり検査する。
- メタ変数を除去した indexed 構文に対する kernel の独立検査は維持する。raw 推論のキャッシュだけで kernel の登録を成功扱いにしない。

完了条件は、複数 module・繰り返し query・テンプレート利用で不要な列挙や再分類が減り、依存順序、循環の拒否、反映・positivity・閉性の検査を維持すること。

## 5. モジュールの遅延実体化との連携

[既存計画](lazy-module-instantiation.md) に従い、instance を作成した時点で全項を複製する処理を、要求された項と依存先の実体化へ変える。上記の lowering の追跡と統合し、getter を遅延化しても `lower_all` が全派生項を要求してしまう状態を避ける。

instance ごとの generative な ID、親 instance の共有、宣言順と可視性、未使用引数の検査、元宣言の全検査を維持する。具体的に実体化した宣言も kernel の検査を通す。すべての項を使うケースでは管理コストが増え得るため、一部利用の改善と合わせて記録する。

この段階は独立した実装単位とし、context や lowering キャッシュの変更と一度に導入しない。

## 6. raw 構文・評価と構文処理の次候補

前段の計測で寄与が大きいものだけ取り組む。

- **raw node のコピー削減。** 既存の Program borrow/reuse API を起点に、読み取り専用の判定と変更のない変換のコピー・割り当てを減らす。同じ partition に割り当てる前に borrow を解放する。共有ノードや interning は保持メモリ・ハッシュの管理費も含めて別に比較する。
- **raw 比較・代入・評価。** 既存の正規化メモ化と比較内 WHNF キャッシュを維持し、残るペア比較・代入の再走査や評価位置の再探索を測る。キャッシュの寿命を広げる場合は環境とメタ変数の状態、比較時の erasure の違いを区別する。Program の評価順序・fuel・反映証明との対応を維持する。
- **構文分類・マクロ。** `elaborate_program_type` などの `SExp` clone と分類試行、マクロの template/capture clone の寄与を測る。借用による分類や不変 template の共有を候補にする。展開結果のキャッシュは hygiene、可視性の順序、module scope、fresh な binder、source span に依存するため、単純に入力 token だけで共有しない。
- **読み込み・構文解析。** `load/library` と parse 単体が主要コストの場合に AST・token のコピーやパス構築を調べる。source 本文は既に `Arc` で共有されている。ファイルの重複使用の拒否やエラー位置を維持し、OS のキャッシュが温まった測定を cold-start の速度とは解釈しない。

## 検証と採用基準

実装段階ごとに `cargo test --workspace` を実行する。追加の回帰テストは、共有 context、メタ変数の代入前後、スコープ変更・試行失敗、宣言更新、複数 module、Program 多相型、反映証明など、変更で結果が変わり得る境界に絞る。

正常系では推論した型・kernel 登録・評価結果を比較し、拒否例では不正な未使用宣言や引数を含めて引き続き拒否することを確認する。診断では source location、goal の context、制約の状態を維持する。

対象ケースの中央値・ばらつき・確保量・保持量に加え、`check/library` と `pipeline/library` の変化を記録する。kernel を同時に変更せず比較し、両計画の変更を組み合わせた値は別に測る。高速化率は事前に断定せず、再現性のある効果が得られた変更を採用する。

## 実装チェックリスト

- [ ] 既存ベンチの基準を保存し、front 内の段階別時間と主要な確保・走査を測る。
- [ ] `front/*` の対象ケースを追加する。
- [ ] メタ変数の展開と未解決判定の作業領域を共有する。
- [ ] context と raw 推論キャッシュのキーを改善する。
- [ ] lowering のキー・分類・context 変換を再利用し、必要なら寿命を延長する。
- [ ] 宣言の全体走査の寄与を確認し、新規・更新宣言の追跡を導入する。
- [ ] module 実体化の寄与に応じて既存の遅延化計画を実施する。
- [ ] 残る raw 演算・マクロ・構文解析の主要コストを改善する。
- [ ] 採用した変更、測定条件、結果、残った課題をこの文書とベンチマーク README に反映する。
