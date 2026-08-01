# formalization TODO

Lean による形式化の今後のロードマップをここにまとめる。
対象は `doc/book/src/system.md` にある foundational theory であり、
目標は最終的に「十分強い集合論的仮定のもとで、この体系の model が作れる」ことを Lean 上で示すこと。

## 現在の状態

- `formalization/lean/RefType.lean`
  - stratified syntax (`TyExpr`, `TmExpr`)
  - `subset s A P : TmExpr`
  - `typeLift A B`, `pred A B t : TyExpr` with `B : TmExpr`
  - sort (`USort`)
  - de Bruijn index
  - shift / substitution の骨格
  - reduction (`TyReduces`, `TmReduces`)
  - judgement を 1 本にまとめた `Derives`
- まだ metatheory は入っていない。
- substitution は total definition だが、代数則はまだ証明していない。

## 方針

- syntax は stratified のまま進める。
- judgement は mutual inductive にせず、`Derives : Context -> Sequent -> Prop` を維持する。
- binder 名は使わず、de Bruijn index を使う。
- named presentation は文書・コメント・将来の pretty printer で扱い、証明本体では使わない。
- strong normalization は狙わず、set-theoretic model による soundness から relative consistency を出す。

## 推奨ファイル分割

現在は次のように分割している。今後の補題もこの責務に従って配置する。

- `formalization/lean/RefType/Syntax.lean`
  - `USort`
  - `VarKind`
  - `TyExpr`, `TmExpr`
  - term-level subset と、明示的な `typeLift` による type-level lifting
  - notation

- `formalization/lean/RefType/Subst.lean`
  - `liftTyFrom`, `liftTmFrom`
  - `substTy`, `substTm`
  - substitution 用の補助定義

- `formalization/lean/RefType/Reduction.lean`
  - `TyReduces`, `TmReduces`
  - `TyBetaEq`, `TmBetaEq`
  - reduction の notation

- `formalization/lean/RefType/Judgement.lean`
  - `Decl`, `Context`, `Lookup`
  - `Sequent`, `Derives`
  - judgement notation

- `formalization/lean/RefType/BasicLemmas.lean`
  - lookup と shift/substitution の基本補題
  - context に関する補題
  - convertibility の基本補題

- `formalization/lean/RefType/Structural.lean`
  - weakening
  - substitution
  - exchange を入れるならここ

- `formalization/lean/RefType/Inversion.lean`
  - generation / inversion lemma
  - sort classification
  - uniqueness 系

- `formalization/lean/RefType/SubjectReduction.lean`
  - subject reduction
  - reduction compatibility

- `formalization/lean/RefType/Model/SyntaxFree.lean`
  - model constructionに必要な意味論的補助定義

- `formalization/lean/RefType/Model/Interpretation.lean`
  - syntax の解釈
  - context valuation

- `formalization/lean/RefType/Model/Soundness.lean`
  - typing / provability soundness

- `formalization/lean/RefType/Consistency.lean`
  - `falseProp` やそれに対応する矛盾命題が導出不能であること

- `formalization/lean/RefType.lean`
  - 上記の import をまとめる入口ファイルにする

## 実装順序

### Phase 1: syntax の安定化

- [x] `RefType.lean` を上記のファイル構成に分割する
- [x] substitution を total definition にする
- [ ] notation を最終的なものに寄せる
- [ ] `Derives` の constructor 本体で `WF`, `HasSort`, `HasType`, `Provable` の補助略記を使う

### Phase 2: substitution 基盤

- [ ] `liftTyFrom` / `liftTmFrom` の基本性質
- [ ] `substTy` / `substTm` の基本性質
- [ ] shift と subst の交換則
- [ ] ty-variable と tm-variable の namespace が干渉しないこと

### Phase 3: structural metatheory

- [ ] lookup weakening
- [ ] derivation weakening
- [ ] substitution lemma for types
- [ ] substitution lemma for terms
- [ ] provability を含む形での substitution

### Phase 4: inversion と分類

- [ ] sort axiom inversion
- [ ] product / lambda / application inversion
- [ ] `hasSort` と `hasType` の分類補題
- [ ] sort の uniqueness / type の uniqueness の候補整理

### Phase 5: reduction 側

- [ ] substitution が reduction を保つこと
- [ ] one-step subject reduction
- [ ] beta-equivalence に関する compatibility
- [ ] 必要なら confluence ではなく convertibility に必要な最小限だけ示す

### Phase 6: model の準備

- [ ] Lean 内でどのメタ理論を仮定するか明文化する
- [ ] `Set_i` を powerset で閉じた universe として読むための仮定を整理する
- [ ] `Prop` を proof-irrelevant に解釈する方針を固定する
- [ ] `Take(X,T,f)` の意味論を non-computational operator として与える

### Phase 7: soundness

- [ ] context interpretation
- [ ] type interpretation
- [ ] term interpretation
- [ ] provability interpretation
- [ ] 各 derivation rule の soundness

### Phase 8: consistency

- [ ] `falseProp` の意味論的解釈を計算する
- [ ] 空文脈で `|- t : falseProp` が起こらないことを示す
- [ ] 必要なら `forall P : Prop, P` に対応する矛盾命題でも同様に示す

## 技術的に注意する点

- de Bruijn index にしたので alpha-equivalence は消えたが、shift/substitution の補題は必須になる。
- substitution は total になった。今後は停止性ではなく、shift/substitution の代数則と simp interface を先に固める。
- `Take(X,T,f)` は domain と codomain を明示する。choice 自体は reduction に入れず、model construction では non-computational operator として扱う。
- `Power A : Set_i` を同じ階層に置くなら、単純な predicative hierarchy では足りない。各 `Set_i` を powerset で閉じた universe として解釈する必要がある。
- Lean の中で示す consistency は、Lean 自身の絶対的 consistency ではなく、十分強い集合論的仮定に対する relative consistency になる。

## 短期タスク

直近でやるべきことは次の順。

1. term/type 両 namespace の shift/substitution 代数則を証明する
2. type-variable carrier membership の derived judgement を設計する
3. erasure soundness と elaboration completeness の前提を確定する
4. derivation weakening / substitution を証明する
