# Crate / Module Environment 実装方針

## 目的

現在の `GlobalEnvironment`、`ModuleManager`、`CheckSession`、`Rc<DefinedConstant>`、
`Rc<InductiveTypeSpecs>` を、次の所有関係へ段階的に移行する。

1. 一つの入力crateを検査するための永続的な `CrateEnv` を作る。
2. `CrateEnv` は、そのcrateに所属するすべての `ModuleEnv` と式arenaを所有する。
3. `ModuleEnv` はmodule parameter、定義、帰納型、子module、名前付きmodule instanceを所有する。
4. `CheckSession` は特定の `ModuleEnv` に所属する局所検査状態として扱う。
5. kernel内部では定義・帰納型を `Rc` ではなく安定したIDで参照する。
6. module instanceは完全適用のみ許し、importごとに新しいidentityを持つgenerative semanticsとする。
7. moduleはソースコードを上から線形に検査し、前方参照を許さない。

この文書は実装時の基準とする。途中で設計を変更する場合は、先にこの文書の不変条件と
データモデルを更新する。

## 確定している意味論

### Moduleは永続的な実体

`ModuleEnv` は検査中だけ存在する一時sessionではない。検査後も `CrateEnv` に保持され、
別moduleからの名前解決、定義展開、帰納型の同一性判定に使用される。

作業中の可変状態が必要な場合は、永続実体と区別して `ModuleBuilder` または
`ModuleSession` と呼ぶ。

### Module instanceはgenerative

同じmoduleを同じ引数で二回importしても、別の `ModuleInstanceId` を発行する。

```text
import X = M(A)
import Y = M(A)
```

このとき `X` と `Y` は異なるinstanceである。特に `M` が帰納型 `T` を公開する場合、
`X.T` と `Y.T` は異なる帰納型identityを持つ。

instanceのcanonicalizationや、引数が同じinstanceの共有は行わない。

### Partial instanceを許さない

module path上のすべてのparameterへ引数が与えられ、全引数の型検査が成功した場合だけ
`ModuleInstanceId` を発行・公開する。

途中まで適用されたmoduleを値として保持したり、後から残りのparameterを与えたりしない。

### Instanceへのアクセスには名前が必要

現在の構文どおり、instanceはimport時に名前を付ける。

```text
import Alias = Root.M(...)
```

instanceのitemには `Alias.item` のように、その名前を経由してアクセスする。
無名instanceを通常の名前解決へ公開しない。

### Module検査は線形

module itemはソースコードの上から順に検査する。

- すでに名前解決可能な定義・帰納型・moduleは検査済みとみなす。
- 後方参照は許す。
- 前方参照は許さない。
- 通常の定義に前方宣言を導入しない。
- 相互再帰は、別途明示的な構文と検査規則を導入しない限り許さない。
- 帰納型自身の再帰参照だけは、検査関数内の構造上のplaceholderで処理する。

## レイヤーごとの責務

### CrateEnv

crate全体で共有する永続データを所有する。

```rust
pub struct CrateEnv {
    arena: Arena,
    modules: Vec<ModuleEnv>,
}
```

主な責務は次のとおり。

- すべての `ModuleEnv` の所有
- AST arenaの所有
- `DefId` / `InductiveId` から実体への検索
- `ModuleId` からmoduleへの検索
- module所有位置とlocal indexから安定IDを発行
- source map、完全修飾名、診断表示用情報を将来保持する基点
- 将来のcrate dependency、revision、incremental compilationの基点

kernelの定義展開・帰納型簡約は `CrateEnv` または、それを抽象化したlookup APIを通して行う。

### ModuleEnv

一つのmoduleについて、検査後も必要な情報を保持する。

```rust
pub struct ModuleEnv {
    id: ModuleId,
    name: SymbolId,
    parent: Option<ModuleId>,
    children: Vec<ModuleId>,

    parameters: Vec<ModuleParameter>,
    definitions: Vec<DefinitionEntry>,
    inductives: Vec<InductiveEntry>,

    names: HashMap<SymbolId, ModuleItemId>,
    instances: Vec<ModuleInstance>,
    imports: HashMap<SymbolId, ModuleInstanceId>,
}
```

`parent`、`children`、import先はRust参照ではなくIDで保持する。自己参照structや、module移動に
よる参照無効化を避ける。

`parameters` にはそのmodule自身が宣言したparameterだけを保持する。祖先moduleのparameterを
含むeffective contextは、親chainから構築する。必要になった場合だけキャッシュする。

### ModuleBuilder / ModuleSession

moduleを線形に構築する作業用オブジェクトである。

```rust
pub struct ModuleBuilder<'crate> {
    crate_env: &'crate mut CrateEnv,
    module_id: ModuleId,
    // 現在までに検査済みのitemと構築途中の情報
}
```

主な責務は次のとおり。

- parameterのelaborationと検査
- source順のitem検査
- 検査済みitemだけを現在moduleのname tableへ追加
- 子moduleの構築
- module instanceの完全適用と名前付き登録
- 検査失敗時の未公開データの破棄

`ModuleBuilder` が存在することは、言語仕様上の前方宣言を意味しない。構築途中のitemは通常の
名前解決へ公開しない。

### CheckSession

`CheckSession` は意味的には現在の `ModuleEnv` に所属する。ただし定義展開やimport先検索には
crate全体が必要なので、内部的には `&CrateEnv + ModuleId` を持つ。

```rust
pub struct CheckSession<'env, 'context> {
    env: &'env CrateEnv,
    current_module: ModuleId,
    context: &'context mut Context,
    caches: CheckCaches,
}
```

`&ModuleEnv` を別に保存せず、必要時に次のように取得する。

```rust
let module = session.env.module(session.current_module);
```

主な責務は次のとおり。

- `check` / `infer` / `infer_sort`
- local contextのpush/pop
- conversion、WHNF、substitutionなどの局所cache
- 現在のmoduleを含む診断情報

親moduleを辿る名前解決は原則としてfront/elaborationで完了させる。kernelへ渡るNodeは
解決済みの `DefId`、`InductiveId`、`ModuleInstanceId` を含む。

## ID設計

最低限、次のIDを導入する。

```rust
#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ModuleId(u32);

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct ModuleInstanceId {
    owner: ModuleId,
    local: u32,
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct DefId { module: ModuleId, index: u32 }

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct InductiveId { module: ModuleId, index: u32 }

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
pub struct SymbolId(u32);
```

### ModuleInstanceId

instanceは、それをimportした `ModuleEnv` が所有する。したがって `owner + local index` で
一意に識別できる。

同じimport文から作られたnested path上の中間instanceも同じowner moduleが所有する。
通常の名前tableへ登録するのは最終instanceだけでよい。

### DefId / InductiveId

実装では `DefId` と `InductiveId` に所有moduleとlocal indexを直接含める。

```rust
pub struct DefId {
    module: ModuleId,
    index: u32,
}

pub struct InductiveId {
    module: ModuleId,
    index: u32,
}
```

generative instanceはmaterialization時に匿名 `ModuleEnv` を作るため、instance itemも通常の
module itemと同じ形式で参照できる。別のlocation tableやinstance用tagは不要である。

現在の `CtorType` は自己型をIDではなく構造上のplaceholderとして保持し、使用時に
`InductiveId` を渡してNodeを構築する。このため、帰納型検査中の予約IDも不要である。

module内のitem tableはappend-onlyとし、検査済みのIDを再利用しない。削除・incremental updateを導入する
場合はgeneration付きIDへ変更する。

## Node表現の変更

最終的に次の `Rc` をNodeから除去する。

```rust
Node::DefinedConstant(Rc<DefinedConstant>)
Node::IndType { indspec: Rc<InductiveTypeSpecs>, ... }
Node::IndCtor { indspec: Rc<InductiveTypeSpecs>, ... }
Node::IndElim { indspec: Rc<InductiveTypeSpecs>, ... }
```

変更後は次の形を基本とする。

```rust
pub enum Node {
    DefinedConstant(DefId),

    IndType {
        inductive: InductiveId,
        parameters: Vec<Exp>,
    },

    IndCtor {
        inductive: InductiveId,
        constructor: u32,
        parameters: Vec<Exp>,
    },

    IndElim {
        inductive: InductiveId,
        elim: Exp,
        return_type: Exp,
        cases: Vec<Exp>,
    },

    // その他のNode
}
```

定義の型・本体は次のように検索する。

```rust
let definition = session.env.definition(def_id);
let ty = definition.ty;
let body = definition.body;
```

帰納型の同一性は `Rc::ptr_eq` ではなく `InductiveId` の等値で判定する。

recordと元の帰納型の対応もpointer searchではなく、`InductiveId`から直接引けるmetadataにする。

```rust
enum InductiveKind {
    Inductive,
    Record(RecordMetadata),
}
```

## 名前のinterning

`Rc<DefinedConstant>` と `Rc<InductiveTypeSpecs>` を除去しても、現在の `Var(Rc<String>)` は
Node clone時にRc操作を発生させる。

de Bruijn index化済みなので、binder名はkernelの意味論には不要である。最終的にはcrate単位の
`SymbolInterner` を導入し、Node内の名前を `SymbolId` にする。

```rust
Node::Var(SymbolId)

Node::Prod {
    display_name: Option<SymbolId>,
    ty: Exp,
    body: Exp,
}
```

ただし、定義・帰納型ID化と同時に行う必要はない。まず大きな `Rc` を除去し、その後に
`Var` / binder名を移行する。

## Module instanceの表現

```rust
pub struct ModuleInstance {
    id: ModuleInstanceId,
    target: ModuleId,
    parent_instance: Option<ModuleInstanceId>,
    arguments: Vec<(ModuleParameterId, Exp)>,

    definitions: Vec<DefinitionEntry>,
    inductives: Vec<InductiveEntry>,
    names: HashMap<SymbolId, ModuleItemId>,
}
```

初期実装では、現在の挙動を保つためeagerに完全instance化する。

- module parameterをすべて代入する。
- instance固有の `DefId` / `InductiveId` を発行する。
- itemの型・本体・帰納型specをinstance側へ保持する。
- source moduleのitemを指す参照を、instance側のitem IDへremapする。
- instance完成後は、参照時に再度module全体を複製しない。

将来、計測結果から必要と判断した場合だけ、item単位のlazy materializationへ変更する。

### Generative identity

import文ごとに次を行う。

1. 新しい `ModuleInstanceId` を発行する。
2. instanceに含まれる各帰納型へ新しい `InductiveId` を発行する。
3. instanceに含まれる各定義へ新しい `DefId` を発行する。
4. 同じtargetと同じargumentsでもIDを共有しない。

これにより、instance固有の帰納型identityが自然に表現される。

### Nested module instance

例えば次のpathを考える。

```text
Root.A(X).B(Y).C(Z)
```

各path componentを完全適用し、privateなinstance chainを作る。

```text
A-instance(X)
└── B-instance(Y, parent=A-instance)
    └── C-instance(Z, parent=B-instance)
```

import名が参照するのは最終 `C-instance` だけでよい。親instanceはparameter substitutionと
item remappingのために保持する。

## Instance生成アルゴリズム

instance生成は、外部から見てatomicにする。失敗したinstanceを `imports` や通常のname tableへ
公開しない。

### 1. Path解決

- current moduleまたはrootを開始地点にする。
- 各path componentの子moduleを解決する。
- 対象はすべて検査済み `ModuleEnv` でなければならない。
- 各componentに必要なparameter数と、与えられた引数名を確認する。

### 2. 引数のelaborationと型検査

- 引数式をimport元moduleのcontextでelaborateする。
- 祖先componentから蓄積したsubstitutionをparameter typeへ適用する。
- `CheckSession` で各引数を検査する。
- 一つでも失敗したら、instance IDを公開せず終了する。

### 3. Materializationの準備

引数検査がすべて成功した後、path上の全module itemを一時値へ変換し、帰納型specも検査する。
この段階では `ModuleInstanceId` やitem IDをまだ発行しない。

materialization時には、source item IDからinstance item IDへのremap tableを順次作る。

```rust
struct InstanceRemap {
    definitions: HashMap<DefId, DefId>,
    inductives: HashMap<InductiveId, InductiveId>,
}
```

module検査は線形で前方参照を許さず、帰納型の自己参照はspec内のplaceholderで表すため、
以前のitemを順にappendしながらremap tableへ追加できる。

### 4. Materialization

各itemへ次の二種類の変換を一度に適用する。

1. module parameter substitution
2. source item IDからinstance item IDへのremap

単なる `exp_subst_map` だけでは不十分である。Node内の `DefId` と `InductiveId` も変換する。

```rust
fn instantiate_exp(
    env: &CrateEnv,
    exp: Exp,
    substitutions: &ModuleSubstitution,
    remap: &InstanceRemap,
) -> Exp;
```

変更されなかった部分木は元の `NodeId` を再利用する。変更されたpathだけ新しいNodeをarenaへ
追加する。

### 5. Commit

すべてのmaterializationが成功したら、次の順に公開する。

1. path componentごとに匿名 `ModuleEnv` を作る。
2. itemをsource順にappendし、発行されたIDをremap tableへ追加する。
3. owner `ModuleEnv` の `instances` へ各componentのinstanceを追加する。
4. 最終instanceのIDを `imports[import_name]` へ追加する。

型検査とspec構築はID発行前に完了させる。import名の重複もmaterialization前に拒否する。

## 線形module検査アルゴリズム

### Module開始

1. 親moduleとmodule名を確認する。
2. `ModuleId` を確保する。
3. module parameterを順番にelaborate・検査する。
4. parameter検査では、それ以前のparameterだけをcontextへpushする。
5. 全parameterが成功したらmodule bodyの検査へ進む。

### Definition

1. 宣言型をelaborateし、sortを検査する。
2. bodyをelaborateする。
3. `session.check(body, ty)` を行う。
4. 成功後に `DefId` を発行し、moduleのdefinitionsとname tableへ追加する。

定義名はbody検査後に公開するため、通常の自己再帰と前方参照はできない。

### Inductive type

帰納型だけはconstructor内から自身を参照するため、検査中は構造上のplaceholderを使う。

1. parameter、index、constructorをelaborateする。
2. constructor内の自己参照をplaceholderとして保持する。
3. positivityとsortを検査する。
4. 成功後にspecをmoduleへ追加し、`InductiveId` とname tableをcommitする。

これは一般的な前方宣言ではなく、一つの帰納型宣言を検査する内部処理である。

### Child module

1. 子moduleを完全に検査する。
2. 成功した `ModuleEnv` だけをcrateへ保持する。
3. 成功後に親のchildren/name tableへ追加する。

子module検査失敗時、親moduleからその子は見えない。

### Import

1. pathと引数を完全に検査する。
2. generativeなinstanceを作る。
3. 成功後にimport名から `ModuleInstanceId` へのmappingを追加する。

同じimport名の重複はエラーとする。

## Lookup API

名前解決とkernel lookupを分離する。

### Front / module lookup

```rust
fn resolve_local(
    env: &CrateEnv,
    current: ModuleId,
    name: SymbolId,
) -> Option<ResolvedItem>;

fn resolve_imported(
    env: &CrateEnv,
    current: ModuleId,
    import_name: SymbolId,
    item_name: SymbolId,
) -> Option<ResolvedItem>;
```

local lookupは現在moduleから親moduleへ辿る。import lookupは現在moduleの
`imports[import_name]` からinstanceを取得する。

### Kernel lookup

kernelはmodule名やimport名を扱わない。

```rust
impl CrateEnv {
    pub fn definition(&self, id: DefId) -> &Definition;
    pub fn inductive(&self, id: InductiveId) -> &InductiveTypeSpecs;
}
```

elaboration後のNodeは解決済みIDだけを持つ。

## Calculus APIへの影響

現在、calculusの多くは `&Arena` だけを受け取る。定義・帰納型をID化すると、展開や簡約には
environment lookupが必要になる。

関数を次の二群に分ける。

### Arenaだけでよい構造操作

- free variable検査
- de Bruijn shift
- Node構造の走査
- 定義展開を伴わないalpha equivalence
- 純粋なNode構築

これらは引き続き `&Arena` を受け取る。

### CrateEnvが必要な意味操作

- DefinedConstantのunfold
- WHNF / normalize
- conversion
- 帰納型eliminator reduction
- infer / check / infer_sort

これらは `&CrateEnv` または `CheckSession` を受け取る。

初期移行では、`CheckSession::arena()` と `CheckSession::env()` を用意し、calculusを段階的に
session/environment対応する。

## Borrow checkerを考慮した登録手順

`&mut ModuleEnv` を保持したまま `&CrateEnv` を `CheckSession`へ渡すと、crate全体とその一部の
借用が衝突する。

次の順序を徹底する。

1. moduleを短時間だけ可変借用し、必要なIDや入力を取り出す。
2. moduleの可変借用を終了する。
3. `CheckSession`で検査する。
4. sessionをdropする。
5. moduleを再び可変借用し、結果をcommitする。

長時間生存する `&mut ModuleEnv` を `ModuleBuilder` のfieldとして保持するより、
`&mut CrateEnv + ModuleId` を保持し、methodごとに短く借用する方が実装しやすい可能性が高い。

```rust
pub struct ModuleBuilder<'crate> {
    env: &'crate mut CrateEnv,
    module: ModuleId,
}
```

必要なら `CrateEnv` のfieldをarena、module table、ID location tableへ分割し、Rustがfield単位の
借用を認識できるAPIにする。

## 一時Nodeの寿命

`CrateEnv` が単一Arenaを所有すると、check、substitution、reduction中に作られた一時Nodeも
crate検査終了まで残る。

初期実装では現在どおり単一Arenaを使う。まずID化とRc除去を完了し、計測する。

その後、必要なら次を検討する。

- CheckSession開始時のarena markと安全なrewind
- local scratch arena
- scratchからglobal arenaへのpromotion
- hash-consing
- Nodeごとのmemoized transform

NodeIdがlocal session外へescapeする場合があるため、安易なrewindは行わない。`infer`結果、
cache、diagnostic、instance materializationへ保存されたNodeIdがないことを証明できるscopeだけ
rewind可能とする。

## Arena::getへの効果と残件

`Rc<DefinedConstant>`、`Rc<InductiveTypeSpecs>` をIDへ変えると、`Arena::get()`によるNodeの
shallow cloneで大きなRc操作は発生しなくなる。

ただし、次は残る。

- `Var(Rc<String>)`
- `parameters: Vec<Exp>`
- `cases: Vec<Exp>`
- その他Node内の可変長Vec

次段階では次を個別に計測する。

- `SymbolId`によるVar/binder名のinterning
- 可変長childrenを別arenaへ置く `SliceId`
- 借用を返すarena API
- immutable/frozen arenaとappend専用arenaの分離

ID化だけで `Arena::get()` のコストが完全になくなるとは仮定しない。

## 移行手順

### Phase 1: IDとenvironmentの骨格

1. `ModuleId`、`ModuleInstanceId`、`DefId`、`InductiveId`を追加する。
2. `CrateEnv`を追加し、既存Arenaを所有させる。
3. 既存 `ModuleManager` のmodule vectorを `CrateEnv.modules` へ移す。
4. 既存の名前解決結果をIDで返せるようにする。
5. この段階ではRc表現を残し、挙動を変えない。

### Phase 2: DefinedConstantのID化

1. ModuleEnvがdefinition実体を所有する。
2. `Node::DefinedConstant`を `DefId`へ変更する。
3. definition lookupを `CrateEnv::definition`へ統一する。
4. unfold、infer、printing、logging、serializationを更新する。
5. `Rc<DefinedConstant>`とpointer serializerを削除する。

### Phase 3: InductiveTypeSpecsのID化

1. ModuleEnvがinductive spec実体を所有する。
2. `Node::IndType`、`IndCtor`、`IndElim`を `InductiveId`へ変更する。
3. 帰納型同一性をID比較にする。
4. record metadataを `InductiveId`から引けるようにする。
5. 自己参照用ID予約とcommitを実装する。
6. `Rc<InductiveTypeSpecs>`とpointer serializerを削除する。

### Phase 4: 永続ModuleInstance

1. 現在の `InstantiatedModule` を `ModuleInstance`へ置換する。
2. `ModuleEnv.instances`と`imports: name -> ModuleInstanceId`を追加する。
3. 完全適用と引数検査をinstance登録前に行う。
4. generativeなitem IDを発行する。
5. parameter substitutionとitem ID remapを同時に行う。
6. `Alias.item` lookupをinstance ID経由にする。
7. 現在のinstance item丸ごとclone経路を削除する。

### Phase 5: CheckSessionとcalculusのenvironment統合

1. `CheckSession`を `&CrateEnv + ModuleId + &mut Context`へ変更する。
2. 定義展開・帰納型簡約をsession/environment経由にする。
3. 純粋な構造操作だけ `&Arena` APIとして残す。
4. local cacheへenvironment revisionまたはcrate identityを含める。

### Phase 6: SymbolIdとArena::get改善

1. `Var(Rc<String>)`を `SymbolId`へ移す。
2. binder表示名を意味論から分離する。
3. perf結果を基にVec clone、SliceId、borrowed getを検討する。

各Phaseはworkspace test、`root.ref`、kernel phase benchmarkを通してから次へ進む。

## 検証すべき不変条件

### IDと所有権

- すべての公開済み `DefId` は必ず有効なDefinitionを指す。
- すべての公開済み `InductiveId` は必ず有効なspecを指す。
- `ModuleInstanceId.owner` は、そのinstanceを所有するModuleEnvと一致する。
- append後にIDの指すitemを移動・並べ替えしない。

### 線形検査

- 後に宣言されたitemは前のitemから参照できない。
- 検査失敗したitemはname tableへ残らない。
- 検査失敗したchild moduleは親から見えない。
- 検査済みitemだけが別moduleから解決できる。

### Generative instance

- 同じmodule・同じargumentsを二回importすると異なる `ModuleInstanceId` になる。
- 各instance内の帰納型は異なる `InductiveId`になる。
- 一方のinstanceのconstructorを他方のinstanceのinductive typeとして使用できない。
- instance内では同じ帰納型参照が同じinstance側 `InductiveId`へremapされる。
- 引数検査失敗時にimport名とinstance itemが公開されない。
- partial applicationは拒否される。

### Contextとsession

- `CheckSession`終了後にlocal context長が開始時と一致する。
- binder下の失敗経路でもpush/popが対応する。
- module parameter contextの順番がde Bruijn indexと一致する。
- 別moduleのcheck cacheを誤って再利用しない。

## 必須テスト

最低限、次のテストを追加する。

1. 親moduleの定義を子moduleから参照できる。
2. 子moduleから後に宣言された親itemは参照できない。
3. nested moduleが祖先parameterと自身のparameterを正しい順序で参照できる。
4. 完全適用されたinstanceだけ登録できる。
5. parameter不足・余分・名前不一致を拒否する。
6. parameter型不一致時にinstanceが残らない。
7. 同一module・同一argumentsの二つのimportが異なるinstance IDを持つ。
8. 二つのgenerative instanceの帰納型を混同できない。
9. instance definitionのbody内参照がsource IDではなくinstance IDへremapされる。
10. instance inductiveのconstructorとeliminatorが同じinstance specを参照する。
11. record projectionが `InductiveId`からrecord metadataを取得できる。
12. `root.ref`が従来どおり検査できる。
13. `Rc<DefinedConstant>`と`Rc<InductiveTypeSpecs>`がsource treeに残っていない。

## 計測

計測手順と結果は引き続き `metrics.txt` に従う。

- `cargo bench -p kernel --bench phases`
- release版 `root.ref` の3回実行
- perfによるself/inclusive overhead
- 日時prefix付きperf.dataとflamegraph

特に次を比較する。

- `Arena::get`
- DefinedConstant unfold
- inductive lookup/reduction
- module instance materialization
- `CheckSession::infer`
- Node cloneとVec clone
- malloc/realloc

`metrics.txt`には解釈を書かず、実行結果だけ追記する。判断と設計上の解釈はこの文書または
別の開発記録へ書く。

## 初期実装で行わないこと

次は今回のenvironment/ID移行と同時には行わない。

- partial module application
- applicative module semantics
- instance canonicalization
- 前方宣言
- 一般的な相互再帰module/definition
- module re-export
- external crate metadata format
- incremental compilation
- parallel module checking
- scratch arenaとGC
- hash-consing

これらを追加する場合でも、`CrateEnv -> ModuleEnv -> CheckSession`という所有関係と、
IDによる参照を崩さず拡張する。

## 実装開始時の最終確認

実装開始前に次を確認する。

1. generative instanceで、同じ引数の二つのinstanceの帰納型を別型とすること。
2. instanceをeager materializationすること。
3. module parameterを当面は現在どおりsubstitutionすること。
4. module instanceをowner ModuleEnvが所有すること。
5. `DefId` / `InductiveId` のmodule部分が所有 `ModuleEnv` と一致すること。
6. 通常のmodule itemは検査成功後だけ公開すること。
7. 帰納型の自己参照placeholderを検査関数内に閉じ込めること。

この確認が変わらない限り、上記Phase順で移行する。
