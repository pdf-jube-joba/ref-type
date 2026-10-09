# ホモロジー代数実装の引き継ぎ

2026-10-09 時点の実装と検証結果。
計画全体は未完了であり、ref-type ライブラリ全体の型検査も未完了。
ブランチは `feat/homological-algebra-plan`。
実装コミット `56770100` に、main の `ed4f28cc` を `601fd938` で統合した。

## 変更範囲

- chain/cochain、写像、ホモトピー、cone、長完全列と圏の構成。
- 射影分解、比較写像、Horseshoe、Ext/Tor、Ext¹ と拡大の対応。
- 整数演算、Smith 計算、有限複体、普遍係数定理の構成要素。
- tensor 複体、符号付き交換、外積、体上の分解と Kunneth の構成。
- 射影分解の tensor 構成。
- 依存する module/structure の引数、名前解決、elaboration、kernel の修正とキャッシュ。
- CLI の `--module`、例題、ベンチマーク、構文と gap の記録。

実装が存在することと、その全体が型検査を通過していることは別の状態。
個別 API の説明は各ライブラリの README と `_plans/gaps.md` を参照。

## main 統合後の検証

```sh
cargo test -p kernel -p resolve -p sema -p syntax -p elaboration --locked -j1
cargo build -p cli --locked -j2
```

Rust テストは 412 件成功し、CLI ビルドも成功。
`cargo fmt --all -- --check` と差分の空白検査も成功。
G22 の明示的引数版は成功し、import した別名を使う版は失敗する。

### 残っている型検査エラー

`Cyclic` の例題は `Resolution Error: Name 'n' was not found in its scope` で失敗する。
発生箇所は `libs/homological_algebra/src/IntegerCyclicResolution/Positive/Projectivity.ref:39`。

```ref
\induction (n: Nat.Nat^) \return Modules.Projective (term (Nat.Nat^::succ n)) \with {
```

射影分解の constructor を利用する個別プロジェクトも同じ名前解決エラーで失敗する。
発生箇所は `libs/homological_algebra/src/NonnegativeChain/Over/ProjectiveResolution.ref:47`。

```ref
\induction (n: N.Nat^) \return Modules.Projective (term n) \with {
```

帰納法の binder と、依存した module 引数の正規化との関係が調査候補。
原因は未確定であり、単純な帰納法の縮小例では再現しなかった。

## main 統合前の検証

以下は統合前の CLI による結果であり、統合後の成功を保証するものではない。

- std、category、algebra、linear_algebra のライブラリ全体の型検査が成功。
- 上記と homological_algebra の構文検査が成功。
- homological_algebra の 22 個のトップ module のうち、Cochain、Integer、Chain、ModuleCategory、Reversal、NonnegativeChain、HomComplex、Resolution の 8 個が成功。
- 外積の二重商への降下と自然性の個別検査が成功し、約 44 分を要した。
- ResolutionTensor の核、全射、因子化、完全性、augmentation、各項の射影性を含む個別検査が成功。
- 射影分解の constructor の個別検査が成功したが、統合後は上記の名前解決エラーが発生。

CLI 統合テスト `cargo test -p cli --test ref_files --locked -j1` は 32 件成功、7 件失敗。
最初の失敗は `homological_algebra_examples_succeed` の Cyclic で、`IntegerCyclicResolution/Positive/TensorHomology/Mapping.ref:9` と `Positive/Tor.ref:3` に関係する `Space` の elaboration エラー。
残り 6 件はライブラリ検査用 mutex の poison による連鎖失敗。
main 統合後の CLI 統合テスト全体は未実行。

## 中断した検査と性能

Field.Tensor の型検査は約 55 分で中断し、終了コードは 143。
この結果は型検査成功として扱えない。
トップ module 別の検査も Ext で中断し、残り 14 module の完了結果はない。
以前のライブラリ全体の検査には終了コード 137 のメモリ不足があった。
実行環境は CPU 4、メモリ上限 16 GiB。
引き継ぎ時点で CLI と cargo の実行プロセスは停止済み。

## 計画上の残作業

- 一般の balanced Tor の比較。
- 整数上の Kunneth の Tor 補正短完全列と例。
- 普遍係数短完全列全体の自然性。
- 体上の選択した分解による Kunneth 写像と標準外積の同一視、選択独立性、自然性。
- main 統合後の名前解決エラー、以前の Space エラー、未完了の型検査と性能の調査。

## ワークスペースの検証記録

ログと縮小例は未追跡の `work/homological-algebra-probes/` に保存してある。
これらは PR に含めず、この文書に主要な結果を記録した。
環境設定は `/workspace/ref-type-env.sh`。

| 記録名 | 結果 |
| --- | --- |
| checkpoint-merged-rust-regressions | 0、Rust 412 件成功 |
| checkpoint-merged-cli-build-final | 0 |
| checkpoint-merged-cyclic | 1、帰納法の n の名前解決エラー |
| checkpoint-merged-native-constructor | 1、帰納法の n の名前解決エラー |
| checkpoint-cli-regressions | 101、統合前の CLI テスト |
| checkpoint-exterior-naturality | 0、統合前 |
| checkpoint-resolution-tensor-complete-points | 0、統合前 |
| checkpoint-field-tensor-module | 143、中断 |

各記録には `.log` と `.exit` がある。
トップ module ごとの結果は `library-module-checks/` にある。
