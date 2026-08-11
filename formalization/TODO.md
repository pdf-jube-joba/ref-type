# formalization TODO

対象の正本は `doc/book/src/system.md` の体系。目標は、Lean 上で universe-like な意味構造を仮定し、正本と導出可能性が同値な presentation の soundness から、空文脈で `falseProp = (P : *^p) -> P` が証明できないことを示すこと。

## 現在の状態

- `RefType/Sort.lean`
  - sort と sort/product の計算規則を定義している。
- `RefType/system.lean`
  - `doc/book/src/system.md` の Lean 実装候補である単一構文・単一 de Bruijn namespace の体系。
  - 現在は context / variable presentation、`propWeak`、`appElim` の前提に差がある。
  - `typeElem` と `typeSort` を含む。
  - `System.falsePropFormed` で `falseProp` の formation は確認済み。
- `RefType/Model.lean`
  - 直接モデルに必要な `UniverseTower` の最初の枠だけを置いている。

## 方針

- 証明対象は `doc/book/src/system.md` に固定し、`System.Derives` は正本との同値を証明してから使う。
- 自然言語の証明は `proof.md`、Lean 固有の設計は
  `lean/formalization.md` に分離する。
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
- [x] `doc/book/src/system.md` の各規則と `System.Derives` の対応を再点検する。
- [x] `takeEq` など、doc/book と前提がずれていないか確認する。
- [ ] 名前付き・右拡張の context / variable 規則と、逆順 de Bruijn / `Lookup` presentation の
  導出可能性の同値を証明する。
- [ ] `propWeak` を admissible weakening へ erase する。
- [ ] `appElim` の追加 sorting premise を product generation と substitution から構成し、
  二 premise 版との導出可能性の同値を証明する。

### Phase 2: 構文メタ理論

- [ ] 一般の renaming / substitution action を定義し、`liftFrom` / `subst` を
  その特殊例として扱う。
- [ ] renaming の identity / composition / binder lifting と substitution の
  基本代数則。
- [ ] lookup weakening。
- [ ] derivation weakening。
- [ ] sorting / typing / provability の substitution lemma。
- [ ] `wf_of_sort` / `wf_of_type` / `wf_of_provable`。
- [ ] `typing_regular_type` / `provable_regular`。
- [ ] sort uniqueness。
- [ ] 一般の type uniqueness の代わりに term sort uniqueness を証明する。
- [ ] product generation と application generation。
- [ ] `proof.md` 3.3 に従って `take_generation` を証明し、現在の `takeEq` から
  元の `takeSet` の nonempty / mapping / constancy premises を復元する。
- [ ] parallel reduction / complete development を定義し、raw `Reduces` の
  confluence と `BetaEq` の joinability を証明する。
- [ ] `proof.md` 3.4 の証明に従い、sorting / typing / provability の subject
  reduction を同時に Lean 化する。`predSubset` は subset generation から
  `A ≃β B` を回収する。

### Phase 3: 意味構造

- [ ] `UniverseTower` に product 閉包を追加する。
- [ ] powerset 閉包を追加する。
- [ ] `El` / `sort_el` と sort closure を追加する。
- [ ] proposition を二値的・proof-irrelevant に読むための `prop_cases` /
  `proof_mem_iff` を追加する。
- [ ] proof product と data product を分けた introduction / elimination / beta law を
  追加する。
- [ ] equality / exists / take に必要な演算と性質を追加する。
- [ ] `takeSet` は global choice ではなく、集合モデルでは `⋃ { f x | x ∈ X }`
  として解釈できることを `UniverseTower` の field に反映する。
- [ ] raw expression interpretation は作らず、導出添字付きの `SortDenotes` /
  `TypeDenotes` / `ProvDenotes` を定義する。
- [ ] `DerivesPlus` の WF field 添字付きの `ValidCtx` を定義し、proof-sort の
  head を canonical `proofVal` にする。

### Phase 4: Denotation と Soundness

- [ ] WF、typing regularity、provability regularity、typed join diagram を保持する
  九種類の完全注釈付き object を定義する。
- [ ] 完全注釈付き object の rank、annotated regularity / subject reduction、erase、
  `Derives -> Nonempty DerivesPlus` という elaboration を証明する。
- [ ] sort / type / provability denotation の存在と一意性。
- [ ] `proof_denotation_canonical`。
- [ ] typing/provability denotation と sorting denotation の regularity coherence。
- [ ] renaming / weakening / substitution の意味論的補題。
- [ ] 完全注釈付き object の rank に関する強い帰納法で denotation existence、fundamental
  theorem、sorting / typed-term の one-step 意味保存、path invariance、coherence
  をまとめて証明する。
- [ ] elaboration と coherence から元の `Derives` の judgement soundness を得る。

### Phase 5: Consistency

- [ ] `falseProp` の意味が false になることを計算する。
- [ ] `not ([] |=₀ falseProp)` を証明する。
- [ ] `not (exists t s, [] |-₀ t : falseProp :: s)` を証明する。

## 注意点

- 一般の type uniqueness は `typeLiftIntro` により成り立たない。必要なのは
  sort uniqueness と outer constructor ごとの generation / injectivity である。
- raw `BetaEq` の問題は `predSubset` 単独ではない。graph application では
  `predSubset` の両辺は domain 外でともに false にできるが、その後の raw beta
  は domain 外で意味を保存しない。raw rule は変更せず、derivable endpoint の
  sorting と全中間点を `TypedJoin` に注釈して処理する。
- `typeSort` により、`falseProp` formation は元体系の通常の導出として扱える。
- `Take(X,T,f)` は reduction ではなくモデル側で解釈する。`takeSet` は
  global choice ではなく、非空かつ定値な image の union として扱う。
- Lean で示すのは Lean 自身や ZFC 自身の無矛盾性ではなく、`UniverseTower` を仮定した相対無矛盾性。
