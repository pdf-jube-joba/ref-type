# 型検査系の現状分析と実装計画

## この文書の役割

この文書は、現在の実装を出発点として、次に何を改善できるか、その目的と採用条件をまとめる。
完了済みの移行手順や作業履歴は扱わない。

計測コマンドと生の実行結果は `metrics.txt` を正本とする。`metrics.txt` には解釈を書かず、分析と方針はこの文書へ反映する。

当面の優先順位は次の通りである。

1. 型体系を変えないend-to-endの軽量化
2. module materializationと代入のscalability改善
3. 名前、Node payload、lookup、cacheの改善
4. checker構造やevaluatorの大きな変更
5. 型体系と利用者向け機能の変更

## 今後も守る設計上の制約

最適化によって次の性質を崩さない。

### Module

- moduleは検査後もcrate内に残る永続的な実体である。
- module instanceは完全適用のみ許す。
- module instanceはgenerativeであり、同じmoduleを同じ引数で二回importしても別identityを持つ。
- instanceはimport名を経由して参照し、partial instanceやinstance canonicalizationは導入しない。
- eager materializationを基本意味論とする。lazy化は、意味論を保てる表現として明確に分離でき、計測上必要な場合だけ再検討する。
- module itemはsource順に検査し、通常の前方参照と暗黙の相互再帰を許さない。
- 検査に失敗したitem、child module、importを名前解決へ公開しない。

### IDと所有権

- 公開済みの`DefId`、`InductiveId`、`ModuleId`、`ModuleInstanceId`は常に有効な実体を指す。
- tableは原則append-onlyとし、IDが指すitemを移動・再利用しない。
- kernelへ渡る項では名前解決を終え、定義と帰納型は安定IDで参照する。
- incrementalityや削除を導入する場合は、generationまたはenvironment revisionを設計してからIDを再利用する。

### 検査とcache

- binder下の検査が成功しても失敗しても、local contextを開始時の長さへ戻す。
- proof/certificateはtyping時に検査するが、通常の計算とconversionでは不要なfieldを走査しない。
- cacheは`static`に置かず、`CheckSession`またはそれを所有するenvironmentへ置く。
- cache keyには結果へ影響するcontext、transparency、environmentのidentityを含める。

## 計測方針

- end-to-endの主要入力は`tests/reals/root.ref`とする。
- release実行の経過時間と最大RSSを記録する。
- sampling profilerには`perf-wsl`を使い、同じ入力を100回実行してsample数を確保する。
- flamegraphは同じ`perf.data`から生成する。
- kernelの各phaseは`cargo bench -p kernel --bench phases`で追跡する。
- `perf.data`とflamegraphには日時prefixを付け、`data/`に保存する。
- 計測専用の内部カウンターを各関数へ恒久的に埋め込まない。benchmark、sampling profiler、必要最小限の一時的なinstrumentationを使う。
- 速度比較では中央値だけでなくminとp95も確認する。

現在の一回実行は`/usr/bin/time`の0.01秒表示付近まで短くなっており、単発値だけでは小さな差を判定できない。one-shotの実態は残しつつ、複数processの合計時間または専用benchmarkも併用する。

## 現状分析

### 最新のend-to-end profile

2026-08-15 15:16の`tests/reals/root.ref`では、release実行の最大RSSは約6 MBだった。100回実行の`perf`は11,353 samples、lost samplesは0だった。

主なself overheadは次の通りである。

| 対象 | self overhead |
| --- | ---: |
| `alloc::fmt::format::format_inner` | 9.52% |
| parser `parse_atom` | 6.73% |
| `String::write_str` | 6.59% |
| `Node` drop | 5.48% |
| `malloc` | 5.16% |
| `fmt::write` | 3.66% |
| `realloc` | 3.47% |
| `Arena::get` | 2.68% |
| `Arena::alloc` | 2.67% |
| `CheckSession::infer` | 1.44% |

kernelのinclusive reportでは`CheckSession::infer`の最大行が7.11%だった。inliningとDWARFにより同名symbolが複数行へ分かれるため、それらを単純に加算はしない。

この入力のend-to-end経路では、calculus単体よりformatting、文字列、parser、allocationの比重が高い。kernelだけをさらに複雑化しても、CLI全体では効果が見えにくい段階にある。

### kernel benchmark

同じ時点の中央値は次の通りである。

| benchmark | median |
| --- | ---: |
| substitution / instantiate | 101.22 us |
| WHNF | 50.15 us |
| normalize | 99.22 us |
| conversion | 54.75 us |
| alpha equality | 2.19 us |
| infer | 11.64 us |

単体ではsubstitutionとnormalizeが比較的大きい。ただし、現在のbenchmarkにはmodule instance materializationがなく、parameter数やitem数に対する伸び方はまだ測れていない。

### コード上に残るコスト

#### ログと出力

- `Logger`は有効levelを持たず、通常実行でもtags、message、payloadを構築してrecordへ追加する。
- ログmacroは`format!`と`Vec<String>`をrecordの要否判定前に作る。
- 正常終了時にも内部recordを列挙し、式を表示用文字列へ変換する。
- 利用者がsource内で要求した`Eval`、`Normalize`、`Check`、`Infer`の結果と、内部diagnostic traceが同じ仕組みに混在している。

formattingと文字列処理がprofile上位にあるため、ここは現在もっとも根拠の強い改善対象である。

#### one-shot CLI

- file modeもTokio runtime上で動く。
- loadとelaborationを二回の`spawn_blocking`で実行する。
- 1processの処理が短いため、runtime初期化とtask切替の固定費が相対的に大きくなり得る。

#### 代入とmodule materialization

- `exp_subst_map`は置換ごとに項全体へ`exp_subst`を適用する。
- module parameterが増えると、同じASTを反復走査する。
- eagerなinstance生成ではdefinition、inductive、recordへparameter substitutionとID remapを行うため、module規模に応じたcloneとallocationが発生する。
- instance materialization専用benchmarkがないため、現時点では実際のscalingを定量化できない。

#### 名前とNode payload

- free variableとbinder表示名には`Rc<String>`が残る。
- module名、item名、import名にも`String`を使う。
- `Node`内のparametersとcasesは`Vec<Exp>`であり、`Arena::get`のshallow cloneでもVecのclone/dropが発生する。
- child moduleとmodule parameterの名前探索は線形である。
- record metadataは`InductiveId`から直接引かず、全module・全itemを走査する。
- front ASTにも`String`、`Box<SExp>`、binderの一時cloneが残る。

`Arena::get`単体は2.68%まで下がった一方、`Node` dropは5.48%、malloc/reallocも上位にある。次に狙うならarenaそのものより、Nodeが所有する文字列と可変長payloadを小さくする方が自然である。

#### contextとcache

- local contextは`Vec`であり、lookupは線形である。
- frontはmodule検査時に親chainからeffective contextを組み直し、parameter列をcloneする。
- context全体のcopyは主要経路から外れているため、現在のprofileだけではpersistent contextを優先する理由は弱い。
- WHNF、conversion、substitution、inferのsession cacheはない。
- 同一計算の反復量とcache hit率はまだ測っていない。

cacheは効果がある可能性があるが、keyと無効化を誤るとcorrectnessへ直接影響する。現時点では表現変更より先に無条件で導入する対象ではない。

#### environmentの堅牢性

- child moduleの検査失敗時、そのmoduleは親から見えないが、確保済みの孤立`ModuleEnv`はcrate内に残り得る。
- `CheckSession`はcurrent moduleを知っているが、module名やsource位置をdiagnosticへ十分利用していない。
- 一時的なreduction/substitution Nodeもcrate arenaに残るため、非常に大きなcrateではarena保持量が増える可能性がある。現在のRSSでは緊急性はない。

## 今後の実装方針

### P0: 計測の分解を補う

#### 目的

0.01秒単位のone-shot値だけで最適化を判断せず、CLI固定費、front、kernel、module materializationを区別する。

#### 方針

1. 空入力、小入力、`root.ref`を複数processで繰り返すend-to-end測定を追加する。
2. parser/elaborationのみのbenchmarkまたは処理本体の時間を取れるharnessを用意する。
3. parameter数、definition数、inductive数を変えられるmodule materialization benchmarkを追加する。
4. 現在のkernel phase benchmarkは継続する。

#### 何のためか

- ログ削減とCLI同期化の効果をkernel改善と分離するため。
- 同時代入が実際にmodule規模へのscalingを改善したか判断するため。
- 小さな絶対時間に対する測定誤差で方針を決めないため。

### P0: ログ経路を分離する

#### 目的

通常検査で不要なformatting、文字列allocation、payload保持をなくす。

#### 方針

1. 出力を次の三種類へ分ける。
   - source上の`Eval`、`Normalize`、`Check`、`Infer`が要求した利用者向け結果
   - 失敗時のdiagnostic
   - 明示的な`--trace`時だけ必要な内部trace
2. `Logger`に有効levelまたはmodeを持たせる。
3. 無効なrecordでは、message、tags、`Exp`、`Context`を構築しない。
4. macroはlevel判定後にだけ`format!`するか、closureまたは`fmt::Arguments`を受け取る。
5. 通常実行では成功した全infer/reductionを内部recordへ保存しない。
6. error frameの文字列化は失敗が確定した時点まで遅らせる。

#### 何のためか

profile上もっとも大きいformattingと文字列処理を直接削減し、通常検査のコストを利用者が要求した出力だけに限定するため。

#### 採用条件

- 通常実行、source上の出力命令、`--trace`の出力契約をtestで固定する。
- end-to-end profileでformattingと`String::write_str`の比率が下がる。
- error messageの情報量を落とさない。

### P0: file modeを同期経路にする

#### 目的

短いone-shot検査からasync runtimeとtask切替の固定費を外す。

#### 方針

第一候補は一つのbinaryを維持し、file subcommandだけ同期関数でload、parse、elaborateする構成である。mainでsubcommandを判定し、server subcommandを選んだ場合だけTokio runtimeを構築する。

依存分離やbinary sizeまで問題になる場合は、同期checker binaryとserver binaryを分ける。

#### 何のためか

file modeの実行時間を入力処理そのものへ近づけ、server都合のruntimeコストをone-shot利用者へ課さないため。

#### 採用条件

- file modeとserver modeの挙動を維持する。
- 空入力と小入力でprocess全体の時間を比較する。
- 構成分離による保守コストが測定上の効果に見合う。

### P1: 一走査の同時代入

#### 目的

module parameter数に比例したASTの反復走査をなくす。

#### 方針

1. 複数の`Var -> Exp`を一つのsubstitution environmentとして引けるようにする。
2. 一回のNode走査ですべてのfree variableを置換する。
3. binder深さに応じたde Bruijn shiftを各replacementへ正しく適用する。
4. 現在の逐次代入と同じ意味になるよう、依存するparameterの置換順序またはsubstitution compositionを明示する。
5. 子が変化しなかったNodeは元の`NodeId`を返す。
6. parameter substitutionと`DefId` / `InductiveId` remapを同じtransformで行えるか比較する。

最初は単純な一走査版だけを実装する。free-variable side table、`SubstId`、結果cache、明示的代入は、その効果を測ってから追加する。

#### 何のためか

- module instance materializationをparameter数に対してscalableにするため。
- substitution benchmarkで大きい木の再構築とallocationを減らすため。
- 後のclosure evaluatorやcacheを導入しなくても得られる低リスクな改善を先に取るため。

#### 採用条件

- 逐次代入との意味の一致をproperty testまたは代表的な依存代入testで確認する。
- binder下のreplacementでcaptureとindexずれがない。
- module materialization benchmarkでparameter数に対する伸び方が改善する。

### P2: 名前とlookupをID化する

#### 目的

文字列比較、`Rc`操作、名前のclone、線形探索を減らし、将来のsource mapとdiagnosticの基盤を作る。

#### 方針

1. crate単位の`SymbolInterner`を導入する。
2. free variable、module名、item名、import名を`SymbolId`で保持する。
3. binderの意味的identityと表示名を分け、表示名は`SymbolId`またはsource spanに置く。
4. moduleごとにchild名とparameter名のindexを持つ。
5. `InductiveId -> RecordMetadata`の直接indexを持つ。
6. lookup APIは大きなfront itemをcloneせず、IDまたはborrowed viewを返す。

#### 何のためか

- `Node` dropと文字列処理を減らすため。
- module/item数が増えても名前解決を線形走査にしないため。
- diagnostic表示用の名前とkernel上のidentityを分離するため。

#### 採用条件

- まずinterner単体を導入し、frontとkernelを一度に全面移行しない。
- serializationとerror表示で元の名前を復元できる。
- parser、lookup、Node drop、RSSのいずれかに測定可能な改善がある。

### P2: Nodeの可変長payloadを分離する

#### 目的

`Arena::get`時のVec clone、Node drop、heap allocationを減らす。

#### 方針

1. Node variantごとのsizeと生成数を測る。
2. parameters、cases、argument列を別arenaの連続領域へ置き、`ExpSliceId`または`(start, len)`で参照する。
3. 頻繁なapplication分解には、binary `App`を維持したspine viewを先に試す。
4. 同一call内では`head + arguments`の分解結果を再利用する。
5. 効果が不足する場合だけ`AppSpine`やtelescopeの物理表現変更を検討する。
6. 同一Nodeが大量に生成されていることを確認できた場合はhash-consingを比較する。

#### 何のためか

- Nodeを固定長かつCopyに近い表現へ寄せるため。
- arena参照のたびに可変長heap payloadをclone/dropしないため。
- beta reductionとconversionのargument列比較を一回の走査にするため。

#### 採用条件

- `Node` drop、`Arena::get`、malloc/reallocがprofile上で十分大きい状態に限る。
- 小さいNodeまで間接参照化してcache localityを悪化させない。
- hash-consingはhash計算とtable lookupの費用を含めて比較し、Node数が減らない入力では採用しない。
- 変更前後のNode size、arena容量、RSSを比較する。

### P2: environment構築をtransactionalにする

#### 目的

失敗したmoduleやinstanceの内部実体をcrateに残さず、将来のincremental検査で扱いやすい不変条件を作る。

#### 方針

1. module bodyを`PendingModule`または`ModuleBuilder`へ構築し、成功時だけ`CrateEnv`へcommitする。
2. 代替案としてtableのmarkを保持し、失敗時に未公開末尾だけ安全にrollbackする。
3. instanceについても型検査、spec構築、重複名検査をcommit前に終える。
4. source mapとcurrent module pathを環境へ保持し、diagnostic frameへ利用する。

#### 何のためか

- 「公開されているか」だけでなく「environment内にあるものは有効」という単純な不変条件を得るため。
- 長時間生存するserver sessionで失敗のたびに孤立moduleを保持しないため。
- incremental update、revision、永続cacheを後から導入しやすくするため。

現在のCLIのRSSと可視性には大きな問題がないため、性能上のP0ではない。

### P3: session cacheとside table

#### 目的

同じNodeのWHNF、conversion、substitution、型推論を一つの検査中に繰り返さない。

#### 方針

導入順は次を基本とする。

1. Nodeごとの構造hashとfree-variable情報
2. session単位のWHNF cache
3. session単位のconversion cache
4. substitution cache
5. `ContextId`導入後のinfer cache

主なkeyは次のようにする。

| 対象 | keyに必要な情報 |
| --- | --- |
| WHNF | `NodeId`、transparency、environment revision |
| conversion | lhs、rhs、比較mode、transparency、environment revision |
| substitution | `NodeId`、substitution identity、binder条件 |
| infer | `ContextId`、`NodeId`、current module、environment revision |

#### 何のためか

- 大きな定義を複数箇所から参照した際の再評価を避けるため。
- conversionの同じ部分問題を再帰的に解き直さないため。
- 将来のserver modeとincremental検査で計算結果を再利用する基盤にするため。

#### 採用条件

- cacheなし/ありを同じbenchmarkで比較する。
- cacheのメモリ増加と速度改善を併記する。
- environment更新後のstale resultをtestする。
- infer cacheはcontext identityがない状態では導入しない。

### P3: 定義のtransparencyを制御する

#### 目的

conversionで theoremや大きな定義を不要に展開しない。

#### 方針

- definitionへ`opaque` / `reducible`属性を導入する。
- 同じ`DefId`同士は本体を開かず一致させる。
- head不一致時だけ、現在のtransparency modeで許された定義を展開する。
- theoremを既定でopaqueにするかは既存コードへの互換性を確認して決める。
- 展開後のWHNF cacheと組み合わせる。

#### 何のためか

証明の大きさを通常の型変換判定へ持ち込まず、定義追加に対するconversion時間を安定させるため。

### P4: evaluatorとcheckerの構造変更

次の案は実装量とcorrectness riskが大きいため、P0からP3の後もkernelが支配的な場合だけ行う。

#### Closure evaluator / NbE

lambda bodyとenvironmentをclosureとして保持し、beta reduction時に代入済みASTを即座に構築しない。conversionはsemantic value同士で比較し、表示や完全正規形が必要な場合だけreadbackする。

目的は、大量のbeta reductionで生じる代入、Node allocation、再走査の削減である。現行WHNF方式と時間、allocation、診断品質、実装複雑度を比較して採否を決める。

#### Bidirectional typing

lambda、proof constructor、subset introductionなどをexpected typeからcheckし、infer後に組み立てた型全体を再検査する経路を減らす。

目的はinfer/check/infer_sort間の重複検査を削減することである。typingが再びprofile上位になった場合に進める。

#### Persistent context

contextを`ContextId`で参照するpersistent stackへ変更し、extendを末尾Node一個の追加にする。infer cacheの安全なkeyとしても使う。

目的は深いbinderでのlookupとcache identityの改善である。現在のprofileでは優先せず、深いcontext用benchmarkで必要性を確認する。

#### Scratch arena

一時Nodeをlocal scratch arenaへ置き、globalへescapeする結果だけpromoteする。

目的は長時間生存するcrate/serverで一時Nodeを保持し続けないことである。`infer`結果、cache、diagnostic、instanceへ保存されたNodeIdを安全に追跡できる設計が前提となる。

## さらに先の方向

### 並列・incremental検査

- module依存グラフから独立moduleを並列検査する。
- declarationのsource hash、依存ID、checker versionを保存する。
- 変更されたdeclarationと依存先だけ再検査する。
- arenaとenvironmentの共有方法、revision、diagnostic順序を先に定義する。

目的は大きなcrateと常駐serverでの再検査時間を減らすことである。現在の一括検査が十分短いため、crate規模が増えてから着手する。

### Build設定

- 配布用releaseとdebug symbol付きprofiling profileを分ける。
- ThinLTO、`codegen-units = 1`、strip、PGOを個別に比較する。
- binary size、clean build時間、実行時間を併記する。

これは実装上の主要ボトルネックを除去した後の仕上げとする。

### 型体系の簡素化

次は性能最適化とは分離し、別branchまたは実験的coreで評価する。

- sortを`Prop | Type(Level)`に近づけ、universe inferenceを導入する。
- subsetをpredicateまたはproof-irrelevant Sigmaとして扱えるか比較する。
- equalityをcarrier明示の`Eq A x y`へ寄せる。
- `TakeSet`、`TakeProp`、`TakeEq`をchoice primitiveまたは公理的定数へ整理する。
- recordをfront側のinductive elaborationに限定する。
- moduleをkernel外の名前解決・parameterization機構として整理する。
- proof termとtyping evidenceを物理的に分離する。

目的はkernelとformalizationの規則数を減らすことであり、現在の受理プログラムや計算規則を変える可能性がある。通常の性能改善と同時には行わない。

### 利用者向けの軽量化

- subsetからcarrierへのcoercionを自動挿入する。
- membership proofをlocal assumptionやreflexivityから探索する。
- proof obligationを本体から分離する。
- implicit argumentとuniverse inferenceを導入する。
- record projectionやmodule parameterを推論する。
- normalizationのfuel、timeout、定義展開深さを設定可能にする。
- 重いconversionに対して型注釈、opaque化、定義分割を提案する。
- エラーに展開した定義と失敗したconversionの最小部分を表示する。

これは実行速度ではなく、利用者が記述・理解する情報量を減らすための方向である。

### Formalizationの軽量化

- core syntaxをde Bruijn表現に固定し、名前付きpresentationとの役割を分ける。
- well-scoped syntaxを使い、renamingとsubstitutionの側条件を減らす。
- admissibleなweakeningを正式な規則から除けるか確認する。
- sortingとtypingを統合する案を比較する。
- raw reductionを保つ案とtyped reductionを採る案を、subject reductionの証明量で比較する。
- Pi、Prop、universe、最小限のequalityから小さなcoreを作り、inductive、subset、Takeを段階的に追加する。
- consistencyが主目的なら、完全なnormalization証明だけでなく直接モデルによるsoundnessを比較する。
- Rust実装と形式化のsyntax、sort表、規則名を可能な範囲で同じ定義から生成する。

目的は、実装上の特殊caseをそのまま証明負担へ持ち込まず、Rust実装とformalizationのずれを小さくすることである。

## 計測結果による選択基準

| 観測結果 | 次に選ぶ方針 |
| --- | --- |
| formattingと文字列処理が上位のまま | ログ分離、遅延format、`SymbolId` |
| 空入力・小入力だけ遅い | file mode同期化、binary/runtime分離 |
| module parameter数とともに急増する | 一走査の同時代入、materialization transform統合 |
| `Node` drop、malloc、`Arena::get`が上位 | `SymbolId`、`ExpSliceId`、spine view |
| 同じWHNF/conversionが繰り返される | session cache、構造hash、free-variable side table |
| 深いcontextでlookupが増える | persistent context、`ContextId` |
| beta reductionと代入が再び支配的 | closure evaluator / NbE |
| 長時間serverでarena/RSSが増え続ける | transactional environment、scratch arena |
| typingが再び支配的 | bidirectional typing、infer evidence再利用 |

大きな変更を「将来役立ちそう」という理由だけで先に入れず、該当する観測結果が得られたときに選ぶ。

## 共通の完了条件

各変更は次を満たす。

- 型体系を変更しない作業では、既存の受理・拒否結果を維持する。
- moduleのgenerativity、完全適用、線形検査、失敗時の非公開を維持する。
- context長、ID identity、cache無効化に関するtestを追加する。
- 変更前後を同じbenchmarkとprofile手順で比較する。
- 改善が誤差範囲または複雑度に見合わない場合は採用しない。

検証コマンドは影響範囲に応じて次を実行する。

```text
cargo test --workspace
cargo clippy --workspace --all-targets -- -D warnings
bash tests/test.sh
bash tests/reals/test.sh
cargo bench -p kernel --bench phases
```

性能変更では、さらに`metrics.txt`冒頭の手順で日時付きの結果、`perf.data`、flamegraphを追加する。

## 直近の着手順

1. module materializationと複数processのend-to-end benchmarkを追加する。
2. 通常実行、利用者要求の出力、`--trace`を分離し、不要なログ生成とformattingを止める。
3. file modeを同期経路にして再計測する。
4. `exp_subst_map`を意味を保った一走査の同時代入へ変更する。
5. 再計測し、`SymbolId`、Node payload分離、session cacheのどれを次に選ぶか判断する。
