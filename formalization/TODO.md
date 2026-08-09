# formalization TODO

対象は `doc/book/src/system.md` に対応する `formalization/lean/RefType/system.lean` の体系。目標は、Lean 上で universe-like な意味構造を仮定し、`System.Derives` の soundness から空文脈で `falseProp = (P : *^p) -> P` が証明できないことを示すこと。

## 現在の状態

- `RefType/Sort.lean`
  - sort と sort/product の計算規則を定義している。
- `RefType/system.lean`
  - `doc/book/src/system.md` に対応する単一構文・単一 de Bruijn namespace の体系。
  - `typeElem` と `typeSort` を含む。
  - `System.falsePropFormed` で `falseProp` の formation は確認済み。
- `RefType/Model.lean`
  - 直接モデルに必要な `UniverseTower` の最初の枠だけを置いている。

## 方針

- 証明対象は `System.Derives` に固定する。
- Lean 内で FOL と ZFC を定義しない。
- ZFC + universe 仮定に相当する部分は、Lean の `structure` として `UniverseTower` にまとめる。
- consistency theorem は `UniverseTower` を仮定した相対無矛盾性として述べる。
- strong normalization ではなく、モデル soundness から無矛盾性を出す。

## 実装順序

### Phase 1: 元体系の点検

- [x] `USort` を `RefType/Sort.lean` に分離する。
- [x] 主入口 `RefType.lean` を `Sort` / `System` / `Model` 中心にする。
- [x] `system.lean` に `typeSort` を追加する。
- [x] `System.falsePropFormed` を証明する。
- [ ] `doc/book/src/system.md` の各規則と `System.Derives` の対応を再点検する。
- [ ] `takeEq` など、doc/book と前提がずれていないか確認する。

### Phase 2: 構文メタ理論

- [ ] `Expr.liftFrom` の基本補題。
- [ ] `Expr.subst` の基本補題。
- [ ] lookup weakening。
- [ ] derivation weakening。
- [ ] substitution lemma。
- [ ] typing/context regularity。
- [ ] product generation と application generation。
- [ ] `TypedStep` / `TypedConv` を定義し、raw `BetaEq` を `typeConv` の根拠にしない。
- [ ] `typedStep_subject` / `typedStep_sound` / `typedConv_sound` を証明する。

### Phase 3: 意味構造

- [ ] `UniverseTower` に product 閉包を追加する。
- [ ] powerset 閉包を追加する。
- [ ] proposition を二値的・proof-irrelevant に読むための field を追加する。
- [ ] equality / exists / take に必要な演算と性質を追加する。
- [ ] `takeSet` は global choice ではなく、集合モデルでは `⋃ { f x | x ∈ X }`
  として解釈できることを `UniverseTower` の field に反映する。
- [ ] expression interpretation を定義する。
- [ ] context valuation を定義する。

### Phase 4: Soundness

- [ ] weakening と substitution の意味論的補題。
- [ ] `TypedStep` と `TypedConv` が意味を保つこと。
- [ ] `System.Derives` の同時 induction で soundness を証明する。

### Phase 5: Consistency

- [ ] `falseProp` の意味が false になることを計算する。
- [ ] `not ([] |=₀ falseProp)` を証明する。
- [ ] `not (exists t s, [] |-₀ t : falseProp :: s)` を証明する。

## 注意点

- `typeSort` により、`falseProp` formation は元体系の通常の導出として扱える。
- `Take(X,T,f)` は reduction ではなくモデル側で解釈する。`takeSet` は
  global choice ではなく、非空かつ定値な image の union として扱う。
- Lean で示すのは Lean 自身や ZFC 自身の無矛盾性ではなく、`UniverseTower` を仮定した相対無矛盾性。
