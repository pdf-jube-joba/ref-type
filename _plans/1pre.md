# ref-type Frontend / Semantic Architecture Plan

# 1. 目的

現在の `front` は、source を読み込み、module を構築し、名前解決・macro expansion・elaboration・metavariable solving を行い、最終的に kernel へ渡すという batch checker として成長してきた。

今後はこの上に、

* Incremental Check
* Package
* Visibility
* LSP
* MCP
* metavariable / goal の問い合わせと操作
* definition / reference / type / diagnostics などの semantic query

を追加したい。

これらは個別の機能ではなく、いずれも

> 現在の source から得られる semantic state を、部分的・反復的・問い合わせ可能な形で扱う

ことを要求する。

したがって、LSP や incremental checker を現在の `front` に追加するのではなく、その前に compiler の内部構造を整理する。

再設計では特に次の問題を解消する。

### Front の処理段階が混ざっている

現在の `SExp` や raw representation は、

* source syntax
* desugared syntax
* unresolved reference
* resolved reference
* elaboration 中の expression
* metavariable を含む expression

など複数の段階を兼ねている。

この構造では、ある source edit によってどの段階から再計算すべきかが曖昧になる。

今後は、

* syntax
* semantic syntax
* elaboration state
* checked calculus

を明確に分離する。

### Elaboration の temporary state が長寿命すぎる

kernel では数万 node 程度である一方、front では数百万 node が生成される。

これは最終的な semantic representation が巨大というより、substitution、reduction、metavariable solving などによって生成される temporary term が長期間 arena に残っていることが大きいと考えられる。

今後は elaboration を declaration-local にし、一つの declaration を処理し終えた時点で temporary state を破棄できる構造にする。

### Project-level information と kernel が結合している

kernel は calculus の正当性を検査する層であるにもかかわらず、現在は `ModuleId`、`DefId`、`ModuleParamId` など project structure に由来する identity を知っている。

これを分離し、package/module/name/visibility といった情報は semantic layer が所有し、kernel は calculus に必要な情報だけを扱う。

### Tooling 用の semantic interface がない

LSP、MCP、interactive proof support が直接 compiler internals を操作すると、それぞれが独自の name resolution や elaboration state を持つことになる。

これを避けるため、project-wide semantic state を問い合わせるための共通 service を用意する。

これを `sema` とする。

---

# 2. 最終的に目指す構造

## 2.1 全体の責務分割

最終的には主に次の crate に分ける。

* `syntax`
* `hir`
* `elab`
* `kernel`
* `sema`

それぞれが扱う情報の lifetime と semantic level を明確に分ける。

### `syntax`

source text の構造を扱う。

主な責務は、

* lexer
* parser
* token
* AST
* span
* source-level identifier

とする。

AST は source に忠実な representation であり、semantic resolution の結果を持たない。

したがって AST に、

* resolved definition
* kernel term
* semantic module ID

などを埋め込まない。

すべての重要な syntax node は十分な source location を持つ。

---

### `hir`

source syntax と elaboration の間にある semantic syntax を扱う。

主な責務は、

* HIR
* Resolved HIR
* `HirId`
* proof-oriented constructs の representation

とする。

HIR は AST より semantic processing に適した形に整理されているが、まだ ordinary name resolution が完了していなくてもよい。

例えば、

```text
\block
\enough
\induction
```

のような readable proof syntax は、expected type や current goal に依存するため、単純な AST lowering の段階では core expression に変換しない。

これらは HIR の node として保持し、elaboration 時に term を構成する。

一方、括弧や純粋に context-free な syntax sugar は AST から HIR へ移る際に除去してよい。

---

### `elab`

Resolved HIR から kernel expression を構成する。

主な責務は、

* metavariable
* temporary MetaTerm
* constraints
* unification
* implicit argument inference
* bidirectional elaboration
* zonk
* elaboration-time reduction

とする。

ここで最も重要な制約は、

> `elab` の state は declaration-local である

こと。

metavariable を含む term は semantic database の恒久的な representation にしない。

---

### `kernel`

trusted calculus の実装だけを扱う。

主な責務は、

* expression
* typing
* conversion
* reduction
* inductive checking
* CBPV-related checking
* calculus に必要な nominal identity

とする。

kernel は、

* source file
* package
* module
* import
* visibility
* user-facing name

を知らない。

---

### `sema`

project 全体の semantic state と compiler subsystem の orchestration を担当する。

主な責務は、

* source/VFS
* module graph
* package graph
* macro environment
* scope
* name resolution
* visibility
* semantic identity
* dependency tracking
* incremental query
* diagnostics
* references
* goals
* persistent cache integration

とする。

`sema` は新しい巨大 IR を所有する crate ではない。

`syntax`、`hir`、`elab`、`kernel` を組み合わせ、

```rust
parse(file)
hir(file)
resolve(item)
elaborate(item)
diagnostics(file)
references(item)
goals(file)
```

といった semantic query を提供する service とする。

---

## 2.2 Source と derived state

処理系の authoritative state は source 側に置く。

通常の compilation では disk 上の source files が入力になる。

LSP では未保存の editor buffer が存在するため、その場合は VFS 上の現在の source snapshot を入力とする。

つまり正確には、

> 現在の source snapshot が意味の唯一の正であり、semantic database や cache はすべてそこから導出される

という構造にする。

`sema` が以前計算した結果を保持していても、それ自体が source と独立した state にはならない。

cache を全削除した場合でも、source から同じ semantic result を再構築できなければならない。

このため filesystem access は compiler 各所から直接行わず、`FileId` と Source/VFS layer を経由する。

例えば、

```rust
trait SourceDatabase {
    fn text(&self, file: FileId) -> Arc<str>;
}
```

のような interface を使用する。

physical path は `FileId` に付随する metadata とし、semantic identity そのものにはしない。

---

## 2.3 AST から Resolved HIR まで

source processing は概念的に次の段階に分ける。

### Parse

source text から AST を生成する。

ここでは名前の意味を解決しない。

### HIR construction

AST から semantic processing に適した HIR を生成する。

この時点で module/item の構造は明確にする。

context-free な sugar はここで除去してよい。

一方、

* proof block
* goal-directed syntax
* macro invocation

など後続処理を必要とする構造は保持する。

### Macro processing

macro expansion には current module/scope と利用可能な macro の情報が必要になる。

したがって、完全な ordinary name resolution より前に、

* module outline
* item outline
* macro namespace

を構築する。

その上で macro expansion を行う。

macro template 内の identifier を早い段階で `ModuleId` や kernel expression に変換する方式は避ける。

hygiene は `SyntaxContextId` のような明示的な context information によって表現する。

generated syntax は definition-site context を持ち、captured syntax は call-site context を保持する。

### Ordinary resolution

macro expansion 後の HIR に対して通常の name resolution を行い、Resolved HIR を生成する。

この時点で source 上の、

```text
foo
```

のような参照は semantic item reference に変換される。

elaborator は module table を検索せず、Resolved HIR から直接参照先を取得する。

---

## 2.4 Semantic identity

project-level identity は `sema` 側で管理する。

少なくとも、

* `FileId`
* `ModuleId` / `ModuleKey`
* `ItemId` / `ItemKey`
* `HirId`
* `GoalId`

などが必要になる。

重要なのは、

> declaration order と semantic identity を分離する

ことである。

現在のように、

```text
DefId = ModuleId + declaration index
```

という形で declaration position を identity にすると、前方への declaration 挿入によって無関係な item の identity まで変化する。

declaration order は処理規則として保持してよいが、identity はそれとは別にする。

なお crate dependency を循環させないため、Resolved HIR が参照する opaque ID の型そのものは `hir` または小さな低レベル crate に置いてもよい。

「どの item を意味するか」という mapping と lifecycle を `sema` が所有することが重要であり、Rust の型定義がどの crate に置かれるかは二次的である。

---

## 2.5 Name resolution と Visibility

name resolution は elaborator から独立させる。

Resolver は、

* local binding
* declaration scope
* module scope
* import
* macro-generated context
* visibility

を扱う。

visibility も Resolver の責務にする。

elaboration の各所に access check を分散させない。

初期仕様としては、

* item は private が default
* `pub` item は package boundary を越えて利用可能
* constructor / field は owner の visibility に従う
* import は default では re-export しない

程度から始められる。

Package はこの Resolver と visibility model の上に構築する。

---

## 2.6 Declaration order

module 内の declaration order は semantic rule として維持する。

module 内では前方から順に environment が増える。

これは macro visibility や通常の declaration lookup に利用できる。

また incremental checking でも、

```text
D0
D1
D2  ← changed
D3
D4
```

に対して、まず単純に `D2` 以降を再処理するという戦略が取れる。

ただし、

```text
D2 だから ID = 2
```

という対応は持たない。

order は processing のための情報、identity は reference のための情報として分離する。

---

## 2.7 Declaration-local elaboration

Resolved HIR の declaration を処理するとき、その declaration 専用の `ElabSession` を作る。

例えば、

```rust
struct ElabSession {
    arena: ElabArena,
    metas: MetaStore,
    constraints: ConstraintStore,
    caches: ElabCaches,
}
```

とする。

一つの declaration について、

1. Resolved HIR を受け取る。
2. MetaTerm を生成する。
3. metavariable と constraint を解く。
4. zonk する。
5. kernel expression に変換する。
6. kernel で検査する。
7. semantic result を `sema` に返す。
8. `ElabSession` を破棄する。

という lifecycle にする。

長期保存するのは、

* final kernel result
* declaration dependencies
* diagnostics
* unresolved goals
* source/HIR mapping

など。

保存しないものは、

* temporary MetaTerm
* substitution result
* temporary WHNF
* unification intermediate state
* declaration-local conversion cache

など。

これによって現在の front arena に数百万 node が残る構造を解消する。

---

## 2.8 Block / proof syntax の elaboration

`\block` などの proof syntax は、AST/HIR lowering の段階で通常の expression に flatten しない。

例えば、

```text
\block {
    \enough A by t;
    ...
}
```

は current goal が分からなければ意味のある core term に変換できない。

そのため HIR では block structure を保持し、elaboration が expected type を受け取った状態で term を構築する。

概念的には、

```rust
fn elaborate_expr(
    expr: ResolvedHirExpr,
    expected: Option<MetaTerm>,
) -> MetaTerm;
```

の中で `Block`、`Enough`、`Induction` などを処理する。

この意味で `elab` は単なる HIR → kernel の mechanical lowering ではなく、goal-directed syntax を core calculus に変換する層でもある。

context-free な sugar は HIR より前で消し、expected type / current goal / metavariable が必要な syntax は `elab` まで残す、という基準を使う。

---

## 2.9 Metavariable と conversion

metavariable は kernel に入れない。

したがって `elab` には一時的な MetaTerm representation が必要になる。

例えば、

```rust
enum MetaTerm {
    ...
    Meta(MetaVarId),
    ...
}
```

のような形になる。

metavariable が存在する以上、elaboration 側の unification は完全には削除できない。

例えば、

```text
?m x ≡ f x
```

から、

```text
?m := f
```

を求める処理は kernel conversion ではない。

一方で definitional equality 自体を `elab` と `kernel` に完全に二重実装することは避ける。

責務を、

```text
meta に関係する equality solving
    → elab

complete term 間の definitional equality
    → kernel
```

に寄せる。

`elab` は、

* occurs check
* meta assignment
* flex-rigid
* flex-flex
* blocked constraints
* zonk

などを担当する。

meta-free な rigid subtree については kernel expression に変換し、kernel conversion を利用できるようにする。

---

## 2.10 Goal を semantic result として扱う

unsolved metavariable は単なる error state として捨てない。

interactive proof support、LSP、MCP から問い合わせられる semantic information として保持する。

例えば、

```rust
struct Goal {
    id: GoalId,
    owner: ItemId,
    span: Span,
    context: Vec<LocalBinding>,
    target: DisplayTerm,
    constraints: Vec<ConstraintInfo>,
}
```

のような representation を `sema` から取得できるようにする。

API としては、

```rust
goals(file)
goal_at(file, position)
goal(id)
```

などを提供する。

将来的に、

* give
* refine
* apply
* case split
* normalize

などもこの interface 上に構築する。

内部の `MetaVarId` は declaration-local なので public identity には使わない。

`GoalId` は `ItemId` と `HirId` などから構成し、source revision が変わっても可能な限り対応付けられる形にする。

---

## 2.11 Partial elaboration

interactive environment では、全 goal が解決されていなくても semantic information が必要になる。

したがって elaboration は、

```rust
struct ElabResult {
    term: Option<kernel::Expression>,
    goals: Vec<Goal>,
    diagnostics: Vec<Diagnostic>,
    dependencies: Vec<ItemId>,
}
```

のような partial result を返せるものにする。

CLI checker は unresolved goal を checking failure として扱える。

LSP/MCP は同じ状態を interactive semantic state として利用する。

---

## 2.12 Kernel の identity model

kernel から project-level `DefId`、`ModuleId`、`ModuleParamId` を取り除く。

通常の definition は、

* classifier
* body

として kernel に渡せればよい。

module parameter は kernel から見ると outer local context にすぎないので、通常の bound variable として処理する。

一方、nominal identity が calculus 上必要なものは kernel-local ID として残す。

例えば、

```rust
struct InductiveId(u32);
struct DatatypeId(u32);
```

とする。

これらは package/module identity を持たず、一つの kernel instance 内でのみ意味を持つ。

必要であれば、

```rust
struct GlobalId(u32);
```

のような opaque marker を通常の global expression に付与することもできる。

対応は `sema` が、

```text
ItemId ↔ kernel::GlobalId
```

として保持する。

---

## 2.13 Kernel term から semantic item を逆引きする

kernel result を `sema` 側で扱いやすくするため、typing semantics に影響しない origin marker を kernel term に持たせてもよい。

例えば、

```rust
Annotated {
    origin: Option<GlobalId>,
    body: Expression,
    classifier: Expression,
}
```

のような形式。

`origin` は conversion では無視される。

これにより `sema` は kernel term 内の global expression から元の semantic item を逆引きできる。

ただし source span は kernel node に埋め込まない。

interning によって一つの kernel node が複数 source occurrence から共有される可能性があるため、source occurrence information は HIR/source map に保持する。

---

## 2.14 Inductive identity

inductive specification の constructor から自身の inductive type を参照するため、specification 完成前に nominal identity を割り当てる必要がある。

そのため、

```rust
let id = kernel.fresh_inductive_id();
let spec = build_spec_using(id);
kernel.register_inductive(id, spec)?;
```

という方式を使う。

`fresh_inductive_id()` は identity だけを発行し、まだ valid declaration として公開しない。

`register_inductive()` が specification を検査し、成功した場合に commit する。

現在 front/raw に存在する `reserve_inductive` の責務を kernel-local identity allocation として整理する。

---

## 2.15 Incremental model

incremental checking はまず declaration 単位から開始する。

expression-level の fine-grained dependency tracking は初期目標にしない。

各 declaration について、

* HIR input
* resolved references
* direct declaration dependencies
* elaboration result
* diagnostics

を query result として扱う。

definition dependency の reverse graph を保持し、ある declaration が変化した場合には依存する declaration を invalidate する。

初期段階では多少過剰に再計算してよい。

### Scope-level invalidation

definition dependency だけでは name resolution の変更を捉えられない。

例えば unqualified name `x` が存在するとき、近い scope に新しい `x` が追加されれば resolution result が変わる。

したがって、

* item の追加・削除
* rename
* import change
* visibility change
* macro declaration change

など scope structure を変更する操作では、その位置以降の declaration を再 resolve する。

negative dependency のような高度な tracking は後から追加する。

---

## 2.16 `sema` を query service にする

`sema` は「一度 mutable environment を構築して最後まで処理する」という API ではなく、query-oriented な API にする。

例えば、

```rust
parse(file)
hir(file)
resolve(item)
elaborate(item)

diagnostics(file)
definition_at(file, position)
references(item)
goals(file)
```

を提供する。

これらの query 間の dependency を追跡し、source が変更された場合に必要なものだけ再計算する。

Salsa を採用する場合は、この query/dependency/invalidation layer に利用する。

---

## 2.17 永続キャッシュ

永続キャッシュは semantic database の正ではなく、

> source から再計算可能だが、再計算コストが高い結果をプロセス終了後も再利用するためのもの

とする。

したがってすべての query result を無条件に保存する必要はない。

初期候補としては declaration 単位で、

* source/input fingerprint
* resolved dependency set
* checked kernel artifact
* diagnostics
* symbol/reference index

などが有用。

parse tree や HIR については、再計算コストと serialization cost を測定してから保存対象にする。

逆に、

* MetaTerm arena
* temporary metavariable assignments
* temporary WHNF results
* declaration-local unification cache

は保存しない。

cache entry は少なくとも、

* compiler/cache format version
* relevant source content hash
* package/configuration input
* dependency fingerprints

から validity を判定する。

cache miss や cache corruption が起きた場合は単に source から再計算する。

Salsa persistence がこの用途を十分満たすならまずそれを利用する。

SQLite は、

* workspace-wide references
* symbol index
* cross-package lookup
* MCP からの横断検索

のように query engine の cache より persistent index として扱った方が自然なデータが必要になった場合に検討する。

Salsa と SQLite の二重 cache を最初から構築しない。

---

## 2.18 Package

Package は semantic infrastructure が完成した後、その上に構築する。

`sema` が、

* PackageGraph
* package dependency
* package root
* package exports
* package visibility boundary

を管理する。

kernel は package を知らない。

package artifact も source から再生成可能な derived artifact とする。

---

## 2.19 Diagnostics

semantic layer では `Result<T, String>` を主要な error representation にしない。

例えば、

```rust
struct Diagnostic {
    code: DiagnosticCode,
    severity: Severity,
    message: String,
    primary: Span,
    secondary: Vec<RelatedDiagnostic>,
    notes: Vec<String>,
}
```

のような structured diagnostics を使用する。

parser、macro expander、resolver、elaborator、kernel bridge が同じ representation を生成する。

CLI はこれを text に render し、LSP や MCP は structured data として利用する。

---

## 2.20 LSP / MCP

LSP と MCP は semantic infrastructure の consumer とする。

LSP は例えば、

```text
hover
    → sema.type_at(...)

definition
    → sema.definition_at(...)

references
    → sema.references(...)

diagnostics
    → sema.diagnostics(...)

goal display
    → sema.goal_at(...)
```

という薄い adapter にする。

MCP も、

* get goal
* inspect context
* inspect type
* find definition
* find references
* refine goal

などを同じ `sema` API に変換する。

LSP/MCP 専用の compiler state は持たない。

---

# 3. 今後の移行順序

全面 rewrite ではなく、既存の checker を動かしたまま責務境界を一つずつ移す。

各 phase は次の phase の前提を作る順序にする。

## Phase 0: 現状の挙動とコストを固定する

構造変更の前に、現在の処理系について最低限の characterization を取る。

確認するもの：

* declaration ごとの elaboration 成否
* kernel node 数
* front/raw node 数
* declaration ごとの node 増加量
* peak memory
* module/declaration processing order
* representative library の checking result

architecture refactor 中に semantic behavior が変わっていないことを確認できる状態を先に作る。

---

## Phase 1: Elaboration を declaration-local にする

最初に現在の raw/metavariable machinery の lifetime を整理する。

既存の representation をそのまま利用してよいので、

```text
module-global raw state
```

から、

```text
declaration-local ElabSession
```

へ移す。

この phase ではまだ AST/HIR を全面的に変更しない。

目的は、

* metavariable state
* temporary arena
* elaboration cache

の lifetime boundary を確立すること。

これは他の semantic redesign から比較的独立しており、現在の数百万 node 問題にも直接効果を確認できる。

---

## Phase 2: Kernel boundary を整理する

次に kernel から project structure を外す。

主な対象：

* `DefId`
* `ModuleId`
* `ModuleParamId`

module parameter を ordinary local context へ移す。

inductive/datatype identity を kernel-local opaque ID に変更する。

必要なら `GlobalId` と transparent origin marker を導入する。

この phase の終了時点で kernel は source/module/package structure を知らない状態を目標とする。

これを早い段階で行うことで、その後の HIR/sema 再設計が現在の kernel API に引っ張られないようにする。

---

## Phase 3: Source layer と syntax/HIR boundary を作る

`FileId` と Source/VFS abstraction を導入する。

その上で現在 `SExp` に混ざっている責務を、

* AST
* HIR
* Resolved HIR
* temporary MetaTerm

へ分離し始める。

まず parser output を純粋な AST とし、semantic state を AST へ書き戻さない構造にする。

同時に span/origin information を整備する。

---

## Phase 4: Macro と Resolver を独立させる

module/item outline を明示的に構築できるようにする。

その上で、

1. macro namespace construction
2. macro expansion
3. ordinary name resolution

を独立した処理として実装する。

macro hygiene を explicit syntax context に移行する。

name resolution を elaborator から除去し、visibility も Resolver に統合する。

この phase で Resolved HIR が実用的な semantic input になる。

---

## Phase 5: `sema` query layer を作る

ここまでに分離した処理を query として統合する。

この段階で、

* FileId
* ModuleId
* ItemId
* HirId
* GoalId

など semantic identity を確定する。

`sema` が、

```text
source
→ AST
→ HIR
→ resolved HIR
→ elaboration result
```

を query dependency として表現できるようにする。

---

## Phase 6: Incremental computation を導入する

declaration-level invalidation を導入する。

まずは、

* source declaration change
* direct definition dependency
* declaration order
* scope change

を使った保守的な invalidation でよい。

この phase で Salsa などの incremental query engine を本格的に利用する。

fine-grained optimization は correctness と architecture が安定した後に行う。

---

## Phase 7: Goal / semantic tooling API を整える

partial elaboration と goal representation を `sema` の正式な API にする。

* goal lookup
* local context
* target
* refine
* apply
* case split

など proof assistance に必要な primitive を追加する。

同時に definition/reference/type/diagnostics の query API も整備する。

これによって LSP/MCP が依存できる semantic surface を完成させる。

---

## Phase 8: Package と永続化を追加する

ModuleGraph、Resolver、visibility、incremental dependency が安定した後に PackageGraph を追加する。

同時に declaration-level の persistent cache を実験する。

まず Salsa persistence など最小限の方法から開始する。

workspace-wide reference/symbol index に別の persistent store が必要だと分かった場合に SQLite を追加する。

---

## Phase 9: LSP / MCP を載せる

最後に LSP と MCP を実装する。

この phase では compiler architecture を新たに作らない。

既に存在する `sema` API を protocol に expose するだけにする。

LSP、MCP、CLI、将来の専用 proof UI が同じ semantic state を参照する状態を最終形とする。

---

# 4. 設計上維持する条件

移行中も最終形でも、次の条件を architecture の invariant とする。

* 現在の source snapshot が authoritative input である。
* semantic database と disk cache はすべて source から再構築可能である。
* AST に resolved semantic object を埋め込まない。
* project-level identity と declaration order を同一視しない。
* ordinary name resolution を elaborator に持たせない。
* unsolved metavariable を kernel に渡さない。
* metavariable を含む term は declaration-local な `elab` state に限定する。
* kernel は package/module/source path/visibility を知らない。
* kernel-local nominal ID と semantic item identity を区別する。
* LSP/MCP は独自の compiler state を持たず `sema` を利用する。
* persistent cache の有無が correctness に影響しない。

この分離を維持した上で、readable proof language の拡張、incremental checking、package、tooling を同じ処理系の上に積み上げられる構造を目指す。
