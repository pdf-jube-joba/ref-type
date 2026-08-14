# 型検査系の軽量化計画

## 目的

現状の「重さ」を次の三つに分け、それぞれ独立に改善する。

1. checker の実行時間・メモリ使用量
2. kernel とメタ理論の複雑さ
3. 利用者が明示しなければならない型・証明・universe 情報の多さ

体系を変更しない最適化を先に行い、その測定結果を見てから kernel の簡素化を検討する。

## 現在の基準値

2026-08-14 に次の値を確認した。

- `cargo test --workspace`: 約 0.55 秒（ビルド済み、67 tests）
- `bash tests/reals/test.sh`: debug build で約 18.44 秒
- `target/release/cli file tests/reals/root.ref`: release build で約 5.54 秒

小さな単体テストは十分速い一方、大きな形式化では正規化、定義展開、代入、AST の clone が増大している可能性が高い。

## 基本方針

- 最初に計測点と回帰ベンチマークを作る。
- 完全正規化ではなく、必要な head だけを評価する。
- 項、文脈、代入を ID と共有構造で表現する。
- メモ化はグローバル変数ではなく、プロジェクトまたはファイル単位の検査セッションが所有する。
- proof/certificate は検査するが、通常の計算・変換可能性判定では走査しない。
- kernel primitive の削減は、既存の意味論を保てるか確認してから行う。

## Phase 0: 計測基盤

### 実施内容

- `tests/reals/root.ref` を主要な回帰ベンチマークにする。
- 小さな beta reduction、深い application spine、大量代入、module instantiate 用のマイクロベンチマークを追加する。
- 次のカウンターを検査終了時に出せるようにする。
  - `infer` / `check` / `infer_sort` の呼び出し回数
  - conversion 判定回数と cache hit 率
  - WHNF・完全正規化の回数
  - 定義展開回数
  - substitution の回数と走査 node 数
  - AST / context の clone 数または概算 node 数
  - definition ごとの検査時間
- release build の値を CI で記録し、大幅な退行を検出する。
- allocation profiler と sampling profiler で上位の処理を確認する。

### 完了条件

- 最適化前後を同一コマンドで比較できる。
- 実数形式化で時間を消費している処理の上位が分かる。

## Phase 1: 低リスクな実装改善

### 1. WHNF ベースの conversion

現在の conversion は両辺を erase して完全正規化してから alpha 同値を比較する。これを次の方式へ変更する。

1. 両辺の head を比較する。
2. head が一致すれば、必要な子だけ再帰的に比較する。
3. head が不一致の側だけ一段展開する。
4. それでも一致しなければ失敗する。

`type_head_normal` も最初に項全体を normalize せず、application spine、`Pred` の subset、inductive eliminator の対象だけを評価する。

### 2. 定義の遅延展開

- 同じ `DefinedConstant` なら本体を開かず同一と判定する。
- 異なる head の比較で必要になったときだけ本体を展開する。
- 定義に `opaque` / `reducible` 属性を導入する。
- theorem や大きな証明は原則 `opaque` にする。
- 展開後の WHNF をキャッシュする。

### 3. proof-aware な比較

- conversion traversal が proof-irrelevant field を直接読み飛ばす。
- conversion のたびに erase 済み AST を構築しない。
- `SubsetIntro` は計算位置では element だけを観察する。
- `TakeSet`、`TakeProp`、`TakeEq` の証明fieldは、typing時には検査するがconversion時には正規化しない。

### 4. ログの軽量化

- 無効なログレベルでは `Exp` と `Context` を clone しない。
- 通常実行では成功した全 infer 結果を `Logger` に保存しない。
- 通常ログは `NodeId`、rule名、短いsummaryだけを保持する。
- 完全な項や導出木は `--trace` 時だけ保存する。
- エラー用文字列とframeは失敗が確定した時点で構築する。

### 完了条件

- 型体系と受理されるプログラムを変更しない。
- 既存testがすべて通る。
- 実数形式化のrelease時間が基準値より明確に短縮する。

## Phase 2: 代入・文脈・module の改善

### 1. 同時代入

現在の `exp_subst_map` のように、変数ごとに項全体を走査する方式をやめる。

- `SubstId` または代入mapを一つ受け取り、一回の走査で全変数を置換する。
- 対象変数がfree variableに含まれなければ元nodeを返す。
- binder下では代入環境をextendする。
- `(NodeId, SubstId)` ごとに結果をキャッシュする。
- 将来的には明示的代入またはclosureによる遅延代入も検討する。

### 2. persistent context

- `Context = Vec<(Var, Exp)>` の全体cloneをやめる。
- contextを `ContextId` で参照するpersistent stackにする。
- extendは新しい末尾nodeを一つ作るだけにする。
- de Bruijn indexまたは一意な `VarId` によりlookupをO(1)にする。
- well-formednessは追加されたbindingだけを検査する。

### 3. module instantiate の遅延化

- import時に全itemを複製・代入しない。
- instantiated moduleを「元module＋parameter environment」として保持する。
- 参照されたitemだけ具体化する。
- `(ModuleId, ParameterEnvironmentId, ItemId)` ごとに具体化結果をキャッシュする。
- module signatureだけを先に検査し、本体は必要時または並列検査時に処理する。

### 完了条件

- parameter数やmodule item数に対して、同じASTの反復走査が発生しない。
- context extendが文脈長に対して定数時間になる。

## Phase 3: 共有 AST とメモ化セッション

### AST 表現

- `Box<Exp>` 中心の所有木から、arena上の `NodeId` または共有された `Rc<Exp>` / `Arc<Exp>` へ移行する。
- hash-consingにより同じ部分項を共有する。
- nodeごとに次をside tableへ保存できるようにする。
  - 構造hash
  - free variables
  - size
  - WHNF
  - sortや型の既知情報
- alpha 同値を安価にするため、kernel syntaxはde Bruijn indexを基本とする。
- 表示用の名前はsurface syntaxまたはsource mapに残す。

### メモ化環境

キャッシュは各再帰関数へ個別に渡さず、`CheckSession` が所有する。

```rust
struct CheckSession<'env> {
    globals: &'env GlobalEnvironment,
    caches: CheckCaches,
    options: CheckOptions,
}

struct CheckCaches {
    whnf: HashMap<NodeId, NodeId>,
    conversion: HashMap<ConversionKey, bool>,
    inferred: HashMap<(ContextId, NodeId), NodeId>,
    substitution: HashMap<(NodeId, SubstId), NodeId>,
}
```

内部の再帰は `self.infer(...)`、`self.convertible(...)` のようなmethod呼び出しにする。

キャッシュの寿命とkeyは次のように分ける。

| 対象 | 主なkey | 寿命 |
| --- | --- | --- |
| WHNF、構造hash、free variables | `NodeId` | AST arenaと同じ |
| 型推論 | `(ContextId, NodeId)` | 検査セッション |
| conversion | `(lhs, rhs, transparency, environment revision)` | 検査セッション |
| substitution | `(NodeId, SubstId)` | 検査セッション |
| module instantiate | `(ModuleId, ParameterEnvironmentId)` | project session |
| 診断途中状態 | request ID | 一回の検査 |

グローバルな `static` キャッシュは使わない。定義追加後のstale result、テスト間の状態漏れ、メモリ保持、並列化の難しさを避けるためである。

### 完了条件

- 同一nodeのWHNFや型を繰り返し計算しない。
- environment更新時に古いcacheを誤って利用しない。
- 一つのproject/file検査中はdefinitionをまたいでcacheを再利用できる。

## Phase 4: checker 構造の整理

### bidirectional typing

- inferできる構文とexpected typeからcheckする構文を分ける。
- lambda、proof constructor、subset introductionはexpected typeからcheckする。
- `infer` の返り値にtypeだけでなくsortやWHNFの既知情報を含める。
- lambda bodyをinferした後、組み立てたproduct全体を最初から再検査しない。
- `erased_convertible`と`can_weaken_to`による重複比較を統合する。
- expected typeがすでに検査済みなら、そのwell-sortedness evidenceを再利用する。

### proof/certificate の分離

- surface/elaboration ASTには明示的なproofを保持する。
- kernelの計算項とtyping evidenceを分離する。
- proofは一度検査した後、通常の実行・conversion・serializationではIDだけを参照できるようにする。
- subset weakeningは暗黙のconversionへ混ぜず、elaboratorが明示的coercionを挿入する案も比較する。

### 並列・incremental検査

- module依存グラフから独立したmoduleを並列検査する。
- declarationごとにsource hash、依存definitionのhash、checker versionを保存する。
- 変更されたdefinitionとその依存先だけ再検査する。
- 並列化する場合はarenaとglobal environmentの共有部分を`Arc`対応させる。

## Phase 5: kernel primitive の削減候補

このphaseは意味論とformalizationへの影響を個別に評価してから実施する。

### sort / universe

- `Set(i)` / `SetKind(i)` を標準的な `Type(i)` / `Type(i+1)` として統合できるか検討する。
- sortを `Prop | Type(Level)` 程度へ縮小する。
- product sortは個別列挙ではなくlevelの `max` とProp規則で計算する。
- universe metavariableと制約solverを導入する。
- universe polymorphismによりlevelごとの定義重複をなくす。
- 実質未使用なら `Univ` / `UnivKind` を削除する。
- computation用sortを追加する場合は、既存sortへの単純追加ではなく仕様世界との二層構造として設計する。

### subset / powerset

次の案を比較する。

1. 現在の集合論的意味を保ち、`PowerSet`、`SubSet`、`Pred`、`TypeLift`のうち最小集合だけをprimitiveにする。
2. subsetを `A -> Prop`、membershipをapplicationとして扱う。
3. refinementをproof-irrelevantな `Sigma x : A, P x` として扱う。

2と3はkernelを大きく単純化できるが、現在意図している集合論的外延性や`Take`の意味を変え得るため、別branchまたは実験的coreで評価する。

### equality

- equalityにcarrierを明示した `Eq A x y` を採用する案を検討する。
- set専用のambient carrier探索を減らす。
- type transportを一般のidentity eliminationで表現する。
- extensional equalityはdefinitional equalityへ入れず、命題的な定理として保つ。

### exists / take

- `TakeSet`、`TakeProp`、`TakeEq`を一つのchoice primitiveと導出規則へ統合できるか検討する。
- `Take`をkernel primitiveではなく、型を持つ公理的定数として置く案を比較する。
- `Exists`をinductive existentialまたはimpredicative encodingへ移せるか検討する。
- proof fieldやderived equalityを計算項へ埋め込まない。

### inductive / record / module

- recordはinductiveへのelaborationとしてfront側に限定する。
- moduleはkernel外の名前解決・parameterization機構として扱う。
- inductiveのkernel primitiveはconstructorとeliminatorの最小部分に絞る。

## Phase 6: formalization の軽量化

- 正本となるcore syntaxをde Bruijn表現に固定し、名前付きpresentationとの導出同値証明を必須にしない。
- admissibleなweakening ruleは正式な規則から除く。
- sortingとtypingを統合できるか検討する。
- raw reductionを維持して複雑な`TypedJoin`を追加する案と、最初からtyped reductionにする案を比較する。
- `Pred`のraw reductionを変更し、subject reductionを直接成立させられるか確認する。
- well-scoped syntaxを用いてrenaming/substitutionの側条件を減らす。
- 最初はPi、Prop、universe、最小限のequalityだけのcoreを形式化する。
- inductive、subset、Takeを一つずつ拡張し、各段階でsoundnessを示す。
- consistencyが主目的なら、完全なnormalization証明より直接モデルによるsoundnessを優先する。
- Rust実装とLean形式化のsort表・構文・規則名を可能な範囲で同じ定義から生成する。

## 利用者向けの軽量化

- subsetからcarrierへのcoercionを自動挿入する。
- membership proofをlocal assumptionやreflexivityから自動探索する。
- proof obligationを本体から分離し、後から埋められるようにする。
- implicit argumentとuniverse inferenceを導入する。
- record projectionやmodule parameterを推論する。
- normalizationのfuel、timeout、定義展開深さを設定可能にする。
- 重いconversionを検出した際、型注釈、opaque化、定義分割を提案する。
- エラーに、展開された定義と失敗したconversionの最小部分を表示する。

## 優先順位

| 優先度 | 作業 | 期待する効果 | 理論への影響 |
| --- | --- | --- | --- |
| P0 | 計測、カウンター、回帰ベンチ | 改善箇所の特定 | なし |
| P0 | WHNF conversion、遅延unfold | 実数形式化の高速化 | なし |
| P0 | proof fieldの非走査、ログ抑制 | clone・正規化削減 | なし |
| P1 | 一走査の同時代入 | module parameter処理の高速化 | なし |
| P1 | persistent context / `ContextId` | context clone・lookup削減 | 小 |
| P1 | module instantiateの遅延化 | import時の複製削減 | 小 |
| P2 | arena / `NodeId` / de Bruijn | 共有とメモ化の基盤 | 中 |
| P2 | bidirectional checker | 重複検査削減 | 中 |
| P3 | proofと計算項の分離 | kernelとconversionの簡素化 | 中～大 |
| P3 | sort、subset、Take等のprimitive削減 | 型体系・形式化の簡素化 | 大 |

## 当面の具体的な着手順

1. 実数形式化にdefinition別時間と各種call countを追加する。
2. `type_head_normal`から先頭の完全正規化を除く。
3. conversionをWHNF同士の遅延比較へ変更する。
4. `DefinedConstant`を必要時だけ展開し、WHNFをcacheする。
5. proof-irrelevant fieldをerase AST生成なしで読み飛ばす。
6. `exp_subst_map`を一走査の同時代入へ変更する。
7. module instantiateをclosure化する。
8. persistent contextと`CheckSession`を導入する。
9. 測定結果を基にarena/de Bruijn移行の費用対効果を判断する。
10. 実装上のボトルネックを除去した後に、型体系そのものの削減案を選ぶ。

最初の目標は、既存の型体系とtest結果を維持したまま、実数形式化のrelease検査時間を安定して短縮することである。
