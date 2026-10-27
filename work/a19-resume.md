# A19 作業の再開

基点 main: bd8fd86d5368968ff22e06f81beb5469bc348623。
専用 worktree: /workspace/ref-type-a19。
ブランチ: codex/a19-complex-hilbert。

A19 に該当する既存 PR・ブランチ・パッケージがないことを確認した。
実スカラー制限、実内積・実 Hilbert 構造、複素 Riesz 表現、実部内積の Cauchy–Schwarz、有界随伴、閉部分空間への直交射影、直交補と商の線形同型は個別検査で成功済み。
零 Hilbert 空間の具体例も成功済み。
有限階数の因子分解、零作用素、和、前後の合成の公開定理も検査済み。
商ノルム、直交補との等長性、最小ノルム代表も成功済み。

未完了: コンパクト作用素と有限階数近似の同値、コンパクト作用素の和・合成・ノルム極限・随伴による閉性、恒等作用素のコンパクト性から有限次元性。
必要な共通 API と理由は公開 README の「コンパクト性に必要な共通 API」に記載した。
全有界性・完備性からのコンパクト性と、有限次元ノルム空間の閉球のコンパクト性・部分空間の閉性の構築は未着手。

検査対象 commit: cdf279257b140afb3e1a158356e513da5e12af9e。
最終検査は両方 accepted。対象22モジュール・315ステップ、依存込み1,057モジュール・12,241ステップを再検査した。
記録: benchmarks/records/complex-hilbert/README.md、target.json、dependencies.json。

再検査コマンド:
```sh
cd /workspace/ref-type-a19
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --module complex_hilbert --full-check-local --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-target-final.json > work/a19-target-final.log 2>&1
/workspace/ref-type/target/debug/cli libs/analysis/complex_hilbert --cache-stats --diagnostics compact --time-limit-seconds 300 --report-json work/a19-dependencies-final.json > work/a19-dependencies-final.log 2>&1
```

workspace の libs/refcache を共有する。
処理系が必要なら `CARGO_TARGET_DIR=/workspace/ref-type/target cargo build -p cli --locked --offline` でビルドする。
未完了のコンパクト性の証明は共有 API の追加が必要なため保留中。
公開 README の最小 API を整備した後、相対コンパクト性と有限階数近似の比較から再開する。
