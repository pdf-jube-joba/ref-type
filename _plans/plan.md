# system.md 準拠の Rust 実装全面書き直し

## 概要

- kernel を PTS の Set/Prop と CBPV Program が型レベルで
  も混ざらない構造へ全面再設計し、front・cli・標準 .ref
  ライブラリを一括で追従させる。

- modules、imports、macros、records、metavariables、既存
  公理など、体系と矛盾しない周辺機能は維持する。

- 旧実装との二重運用は行わない。新体系に存在しない
  \RfType、\RfTerm、証明引数付き5引数 \run は即時廃止
  し、専用の移行エラーを返す。

## Core と公開 API

- 単一の Exp/Node を、型付きIDを持つ独立カテゴリへ置き換
  える。
    - SetTermId
    - ValueTypeId / ComputationTypeId
    - ValueId / ComputationId
    - ProgramTypeId / ProgramTermId

- Set と Program にそれぞれ SetContext、ProgramContext
  を設ける。Program context は type/value entry のみを持
  ち、PTS entry との混在を kernel API 上で不可能にする。

- raw syntax と検査済み表現を分離する。checker は
  Pending<T> と provability obligations を生成し、すべて
  の証明を検査した後だけ Checked<T> を返す。環境には
  Checked な宣言だけを登録する。

- checker を SetChecker と ProgramChecker に分割し、
  sorting、PTS typing、Program type formation、value/
  computation typing、well-termination を個別 API として
  公開する。

- reflection は AST node ではなく、raw Program syntax か
  ら raw Set syntaxへの reflect_type、reflect_value、
  reflect_computation、reflect_context として実装する。
  de Bruijn index により capture を防ぎ、global
  definition は循環検出付きで透明に展開する。

- evaluator は停止しない通常 Program に備えて予算付きに
  し、Normal または OutOfFuel を返す。convertibility で
  も予算切れを不一致扱いせず構造化エラーにする。

## 体系の実装

- Sort の axiom/product relation を system.md と完全一致
  させ、現在許可されている余分な SetKind → Prop product
  を拒否する。

- Set/Prop は通常の β 簡約と全 compatible closure、
  Pred、RunStep recursor、Set run/runCase、帰納型の規則
  を実装する。definitional equality はその対称・推移閉包
  を正規化で判定する。

- Program は value/computation type、thunk/force、
  return、function、sequence、value-let、RunStep、run/
  runCase、case を独立に検査し、指定された evaluation
  context による weak CBV だけを行う。Program の run 自
  体には停止証明を持たせない。

- well-termination は Program typing と、RfCtx(Delta) 上
  での反射項の PTS typing の両方を検査する。通常の
  Program 宣言は typing だけで受理し、box 化するときに
  well-termination を要求する。

- Boxed Program に
  \Box(P)、\box(P,p)、\Force(P,b)、\boxapp(f,a) を追加す
  る。payload の Program type/term は閉じていることを確
  認し、box step、terminal force、boxed application、専
  用 compatible context を実装する。

- \Proof P、Set run、subset introduction、Take、box 内の
  反射された run が要求する provability premise は
  obligation として収集する。

- surface の証明入力は次に統一する。

  proof {
    - goal (local: Context): Proposition := proof-witness;
  }

  \by term を一般の「項による provable」証明とし、既存の
  exists、subset、equality、Acc 関連の証明構文は proof-
  witness DSL として維持する。goal は context と
  proposition の definitional equality で対応付け、同一
  goal は共有する。未解決・未使用・曖昧な証明、循環する
  obligation は宣言エラーにする。

- Program 帰納型は parameter、constructor、strict
  positivity、名前の一意性、Set 側の同名鏡像、
  constructor/case reflection を実装する。関数 domain 内
  の再帰 occurrence は必ず拒否する。鏡像 case に必要な非
  依存 case は生成するが、system.md の課題に残る一般の
  dependent induction、未規定の universe policy、高水準
  な構造再帰 elaboration は実装せず明示的な unsupported
  error にする。

## Front、CLI、既存資産

- parser → macro expansion → 名前解決/category
  elaboration → kernel check → proof-block discharge →
  declaration publish、という処理順に整理する。

- module が PTS と Program の宣言を含むことは許すが、各
  宣言には対応カテゴリの parameter/context だけを渡す。
  cross-category 参照は box または規定された reflection
  処理以外では拒否する。

- Program datatype と Set 鏡像は別 namespace/category と
  して同じ表示名を利用し、期待カテゴリから解決する。
  reflection 専用の surface termは設けない。

- records、modules/imports、macros、implicit
  metavariables、構造化エラー、tracing、CLI の file/
  serve と /run API は新 kernel API 上へ移植する。

- lib/Nat.ref は Certified parameter、\RfType、\RfTerm、
  5引数 \run を除去し、停止証明なしで ordinary Program
  run を型付けする。他のライブラリは新しい category 分離
  に必要な箇所だけ修正する。

## テストと受け入れ条件

- sort/product relation の許可・拒否、universe lift、PTS
  β/compatible reduction、conversion。

- Set/Program context 分離と、双方からの不正な cross-
  category 参照拒否。

- Program の各 CBV context、thunk/force、sequence、
  case、複数段 run、fuel exhaustion。

- 全 Program type/value/computation constructor の構造的
  reflection、binder capture 回避、Program inductive の
  鏡像と case。

- ordinary Program run は証明なしで通り、well-
  termination・Set run・box は適切な Acc goal が未解決な
  ら失敗し、proof block で解決すれば通ること。

- box の閉包検査、value/computation box、box step、
  terminal force、boxed application、不正な型の組み合わ
  せ。

- proof goal の共有、局所 context 照合、definitional
  equality、未解決・余分・循環証明の診断。

- positivity、constructor completeness、重複名、未規定の
  dependent mirror/induction に対する明示的エラー。

- 旧 \RfType、\RfTerm、5引数 \run が移行案付きで失敗する
  parser tests。

- 最終確認は cargo fmt --check、cargo test --workspace、
  cargo clippy --workspace --all-targets -- -D
  warnings、cargo run --quiet -- file lib/root.ref をす
  べて成功させる。