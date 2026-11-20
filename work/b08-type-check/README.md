# B08 型検査の検証記録

2026-11-20 に `grassmannian_cells` の既存実装を修正し、B08 本体と依存閉包の型検査が成功した。
検証対象のソースコミットは `5deadd6563878d1a010b9b628b7e9d68229a9cfe`、開始時の `origin/main` は `4640f66e357691eadaec5632aa07bd0eff643979` である。
この記録と B08 の README は、上記ソースの検証後に追加した文書である。

## 修正範囲

ソース変更は `libs/geometry/grassmannian_cells/src` の110ファイル、546行追加・403行削除に収まる。
兄弟・親モジュールの参照、宣言順序と依存循環、refinement の等式端点、帰納法の引数、連続写像の合成の定義域、依存型の移送を修正した。
既存の命題と仮定を保ち、最大値の述語、境界の補助証明、向き付き実 Grassmannian の family の核を依存順に配置した。
`Reduction.At.normalFormExists` と `rankBound` は `Reduction` に移し、`Characteristic.Algebra.boundaryLower` は `Characteristic.Boundary.exists` として分離した。
B08 のモジュール数は221から225になった。

公理の追加はなく、B08 ソース中の既存公理の使用箇所数は修正前後とも `classicalIndefiniteChoice` が3、`funext` が87、`setext` が26である。
処理系、検査ドライバー、他のパッケージのソースはこの枝では変更していない。

## 検査結果

| 対象 | 結果 | 検証 / 対象 | 実検査 | キャッシュ再利用 | 未確認 |
| --- | --- | ---: | ---: | ---: | ---: |
| 空行除去前の B08 通常 CLI | accepted | 1,206 / 1,206 | 225 | 981 | 0 |
| 最終ソースの B08 通常 CLI | accepted | 1,206 / 1,206 | 0 | 1,206 | 0 |
| 最終ソースの全体実行内 B08 スコープ | accepted | 1,206 / 1,206 | 225 | 981 | 0 |
| 一時統合の全体検査（容量不足） | failed | 13,276 / 15,750 | 1,969 | 11,307 | 2,474 |
| B08 と依存閉包 | accepted | 7,852 / 7,852 | 0 | 7,852 | 0 |
| B08 ブランチの libs 全体 | failed | 11,895 / 15,749 | 225 | 11,670 | 3,854 |
| B08 と G06 のローカル一時統合の libs 全体 | interrupted | 13,276 / 15,750 | 1,969 | 11,307 | 2,474 |

最初の通常 CLI の実検査225件は B08 の全225モジュールに相当し、そのソースは `8b6e500ab829a30b301d82c614b714d2475b9532` にコミットした。
その後、分離した二つの境界証明ファイルの末尾空行だけを除いた `5deadd6563878d1a010b9b628b7e9d68229a9cfe` 上で、通常 CLI と各ドライバーを新規実行した。
最終ソースの全体実行でも B08 全225モジュールが `checked_modules` に記録され、実検査が成功した。
末尾空行除去前の実行は `evidence.json` の `*-before-format` と対応する raw archive に分けて保存し、表の最終結果と合算していない。
実検査は CLI の `checked_modules` に記録されたモジュール、キャッシュ再利用は検証済みキャッシュから受理したモジュールであり、両者を区別する。
実検査の内部でも検証済み環境チェックポイントが再利用され、最初の B08 通常 CLI では1件であった。
ドライバーの `--resume-report` による前回 report の引き継ぎとは異なる。
各ドライバー実行は新しい state directory で開始し、`libs/refcache` の正規キャッシュを使用した。
一時統合の容量不足後の再開に限り、同一入力の report を `--resume-report` で引き継いだ。ソース snapshot・バイナリ・対象リストをドライバーが照合し、完了済み13,276件の結果と実検査／再利用の分類を保持した。再開後の経過時間・実行統計は再開した呼出しのみを表す。
ソース変更前の resume report は使用していない。
最終の各実行でキャッシュ保存失敗と破損キャッシュ読み出しはともに0である。

B08 単独の libs 全体検査は B08 と次の `bundle_classification` まで成功し、次の既知 G06 エラーで停止した。
未確認3,854件の全リストとパッケージ別内訳は raw archive と `evidence.json` に含む。

```text
Resolution Error: child module 'Frame' was not found
libs/geometry/tubular_neighborhoods/src/Euclidean/On/Of/With/Compact.ref:9:1
```

### ローカル一時統合

一時統合先はローカル枝 `verify/b08-g06-integration-final`、コミットは `1e812671ed7d00355c0b2f56f753c3d0664eab76` である。
B08 ソース `5deadd6563878d1a010b9b628b7e9d68229a9cfe` に、[G06 PR #85](https://github.com/pdf-jube-joba/ref-type/pull/85) のソースコミット `6c55189d9908022e04f88e22357c61f81539302b` だけを cherry-pick した。
G06 の証跡のみの先端 `8f11b8520dc6638ee677924ed66f214d2d415250` は適用していない。
B08 のソースが上記 B08 コミットと一致し、G06 のソースと `gaps.md` が上記 G06 コミットと一致することを確認した。
この一時統合は B08 PR の変更範囲には含まれない。

一時統合は 13,276 / 15,750 の完了後に停止し、残る 2,474 モジュールは未確認である。
停止理由は次のとおりであり、B08 と依存閉包の成功とは分けて扱う。

```text
interrupted; log /workspace/b08-check/repository-integrated-recovered/20261120T190030.866791Z/00001-cohomology_thom.Thom.Real.DirectSum.log; rerun the same command
```

末尾空行除去前の一時統合 `6fa1b42ffce0895c3c08b5f2a36a22d06a82d2fa` はメモリ目安8,192 MiBで実行し、12,618 / 15,750の完了後、`cohomology_thom` の実検査中にメモリ退避が頻発したため中断した。
この中断は型エラーではなく、部分完了を最終結果へ合算していない。
検証済みチェックポイントを保持し、最終ソースの通常 CLI・依存閉包・単独全体検査はメモリ目安12,288 MiBで実行した。
同じ一時統合上の次の実行も `cohomology_thom` で既定128 MiBの式グラフのページ退避が多かったため、12,618 / 15,750完了時点で中断した。
最終の一時統合の全体検査は、既存設定 `REF_TYPE_GRAPH_RESIDENT_MIB=1024`、メモリ目安14,336 MiBの新規ドライバーで実行した。
さらに大きな一時統合スコープを既存ドライバーの `--max-scope-targets 128` と `--split-package` で分割し、同じ全15,750モジュールを新規実行した。
分割した実行は5時間強の検査後、空き容量256 MiB未満のドライバーの保護機能で13,276 / 15,750件の時点で停止した。型エラーによる停止ではない。
プロセス終了後に標準 CLI のキャッシュ整理を実行して空き容量を回復し、同一入力の report だけを引き継いで再開した。
再開後も別パッケージの同じ証明でメモリ制限近くの処理が続いたため、再開実行は明示的に中断した。中断時は16 GiB制限に対してメモリ使用量約15.73 GiBであった。
再開実行が新たに受理したスコープは0件で、13,276件は入力照合済みの前回結果の引き継ぎである。進行中スコープでキャッシュから受理した710件は、ドライバーの完了件数へ加算していない。
この中断を型エラーとは扱わず、全体成功も主張しない。
ソースを固定した一時統合の各実行は、検査対象ソース、処理系バイナリ、検査ドライバーの SHA-256 が一致する。

## 実行コマンド

作業ディレクトリは `/workspace/ref-type` である。
長い実行の標準出力と標準エラーは別々のファイルへ保存した。
一時統合で残る未確認範囲は `cohomology_thom` 161、`compact_support_k` 272、`clutching_linearization` 330、`k_theory_thom` 850、`relative_k_theory` 523、`bott_product` 117、`periodic_k_theory` 130、`topological_k_theory` 91モジュールである。

```sh
RUSTUP_HOME=/workspace/.ref-type-toolchain/rustup CARGO_HOME=/workspace/.ref-type-toolchain/cargo /workspace/.ref-type-toolchain/cargo/bin/cargo +1.100.0 build --locked --release -p cli -j 4 > /workspace/b08-check/build.stdout 2> /workspace/b08-check/build.stderr

target/release/cli libs/geometry/grassmannian_cells --module grassmannian_cells --cache-dir libs/refcache --memory-mib 12288 --report-json /workspace/b08-check/b08-formatted.json --diagnostics compact > /workspace/b08-check/b08-formatted.stdout 2> /workspace/b08-check/b08-formatted.stderr

python3 scripts/check_all.py libs/geometry/grassmannian_cells --state-dir /workspace/b08-check/package-final-formatted --cache-dir libs/refcache --memory-mib 12288 --cache-budget-mib 12288 > /workspace/b08-check/package-final-formatted.stdout 2> /workspace/b08-check/package-final-formatted.stderr

python3 scripts/check_all.py libs --state-dir /workspace/b08-check/repository-main-formatted --cache-dir libs/refcache --memory-mib 12288 --cache-budget-mib 12288 > /workspace/b08-check/repository-main-formatted.stdout 2> /workspace/b08-check/repository-main-formatted.stderr

git switch -c verify/b08-g06-integration-final 5deadd6563878d1a010b9b628b7e9d68229a9cfe
git cherry-pick 6c55189d9908022e04f88e22357c61f81539302b

REF_TYPE_GRAPH_RESIDENT_MIB=1024 python3 scripts/check_all.py libs --state-dir /workspace/b08-check/repository-integrated-split --cache-dir libs/refcache --memory-mib 14336 --cache-budget-mib 12288 --max-scope-targets 128 --split-package cohomology_thom --split-package k_theory_thom --split-package relative_k_theory --split-package clutching_linearization --split-package compact_support_k --split-package periodic_k_theory --split-package topological_k_theory --split-package bott_product > /workspace/b08-check/repository-integrated-split.stdout 2> /workspace/b08-check/repository-integrated-split.stderr

target/release/cli libs/std --module std --module-only --cache-dir libs/refcache --memory-mib 3072 --cache-budget-mib 12288 --report-json /workspace/b08-check/cache-recovery.json --diagnostics compact > /workspace/b08-check/cache-recovery.stdout 2> /workspace/b08-check/cache-recovery.stderr

REF_TYPE_GRAPH_RESIDENT_MIB=1024 python3 scripts/check_all.py libs --state-dir /workspace/b08-check/repository-integrated-recovered --cache-dir libs/refcache --memory-mib 14336 --cache-budget-mib 12288 --max-scope-targets 128 --split-package cohomology_thom --split-package k_theory_thom --split-package relative_k_theory --split-package clutching_linearization --split-package compact_support_k --split-package periodic_k_theory --split-package topological_k_theory --split-package bott_product --resume-report /workspace/b08-check/repository-integrated-split/20261120T134249.946374Z/report.json > /workspace/b08-check/repository-integrated-recovered.stdout 2> /workspace/b08-check/repository-integrated-recovered.stderr
```

## 証跡

[evidence.json](evidence.json) にコミット、実行件数、入力 snapshot・バイナリ・ドライバー・archive の SHA-256、最初の診断、未確認件数と内訳を保存した。
`raw/` の各 archive は driver report、CLI ごとの report とログ、標準出力と標準エラー、対象リスト、未確認リスト、入力 snapshot のハッシュを含む。
入力 snapshot 本文はソースコミットから再生成できるため archive には重複収録していない。
再開実行の引き継ぎスコープの生の report とログは、容量不足で停止した実行の archive に収録している。

- [B08 全225モジュールの実検査](raw/b08-normal.tar.gz)
- [最終ソースの B08 通常 CLI](raw/b08-final-normal.tar.gz)
- [B08 と依存閉包](raw/package-final.tar.gz)
- [B08 単独の libs 全体](raw/repository-main.tar.gz)
- [ローカル一時統合の libs 全体](raw/repository-integrated.tar.gz)
- [release ビルド](raw/build.tar.gz)
- [最初の修正後の依存閉包の失敗記録](raw/package-initial.tar.gz)
- [末尾空行除去前の依存閉包](raw/package-before-format.tar.gz)
- [末尾空行除去前の B08 単独全体検査](raw/repository-before-format.tar.gz)
- [末尾空行除去前の一時統合・中断記録](raw/integration-before-format.tar.gz)
- [式グラフ常駐予算変更前の一時統合・中断記録](raw/integration-before-graph.tar.gz)
- [スコープ分割前の一時統合・中断記録](raw/integration-before-split.tar.gz)
- [容量不足で停止した一時統合](raw/integration-before-recovery.tar.gz)
- [容量回復時の標準キャッシュ整理](raw/cache-recovery.tar.gz)

初回の依存閉包検査は `c6d1eeebe760d2de351a1a0c1808793e6ccd9036` を対象とし、`Symbols.FreeCount.Fiber` の兄弟 `Column` の参照で停止した履歴である。
この初回の失敗と以前の G06 の全体検査は、今回の最終検証件数には加算していない。
