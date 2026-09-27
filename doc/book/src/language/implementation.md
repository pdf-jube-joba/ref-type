# 言語処理系

`syntax` が構文解析、`resolve` が名前解決、`elaboration` が暗黙引数・block・module の具体化を担当する。
型検査、単一化、代入、簡約、reflection は `kernel` の共通項に対する操作である。
`sema` はソースの snapshot と semantic query を管理し、CLI と LSP がその結果を利用する。

## 項と定義

sort・型・項・証明は、共通の `Expression` arena に保存する。
定義 arena は文脈・宣言型・本体を保持し、項からは `DefinitionId` と明示的な文脈引数で参照する。
elaboration は名前・ソース位置・module の所属を ID に対応付ける。
Program の反映先も検証済みの定義として登録する。

## 穴と宣言の確定

`_` は出現ごと、番号付きの穴は宣言内で共有する contextual metavariable とする。
メタ変数の文脈引数を通じた単一化と、保留制約の再実行は kernel が処理する。
公開 `check`・`infer` は未解決の項・型・文脈・証明をエラーにする。
宣言の確定時には、自動生成したメタ変数と残存制約を含めて `finish` を通す。

`?` は通常の単一化で解き、elaboration が文脈・期待型・制約・求まった解を表示する。
`?` を含む module は、解決済みの場合もゴールの診断を返して失敗する。

API と検証例は [kernel](../../../../src/kernel/README.md) と [elaboration](../../../../src/elaboration/README.md) の説明を参照する。
