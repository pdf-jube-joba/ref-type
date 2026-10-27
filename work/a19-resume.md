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
距離空間の有限ネットと全有界性を追加し、コンパクト集合の全有界性を個別検査した。全有界性・完備性からのコンパクト性と、有限次元ノルム空間の閉球のコンパクト性・部分空間の閉性は引き続き構築する。

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
次は標準的な相対コンパクト性から始め、全有界性・完備性と有限次元部分空間の補題を既存 API から証明する。K03 の既存束基盤は変更しない。
全有界性の個別検査: `cli libs/topology/metric --module metric_spaces.MetricSpace.Compactness.TotalBounded --cache-stats --diagnostics compact --time-limit-seconds 90` は終了コード 0。

追加進捗: 距離空間の相対コンパクト性、部分集合・連続像による保存、コンパクト作用素の標準定義、像の全有界性、零値作用素のコンパクト性を実装し、各対象および零空間の例を個別検査した。次は有界作用素の連続性を構成し合成に適用する。さらに完備・全有界から閉包コンパクト、有限次元閉球と有限次元部分空間の閉性を証明する。

有界作用素の連続性と、有界作用素によるコンパクト作用素の後合成を実装し、各モジュールの個別検査が成功した。前合成・和・ノルム極限・随伴・恒等作用素有限次元性は未実装。長い検査ではソースを固定し、対象と依存先、metric の回帰を実行して結果を記録する。

ソース commit 80cf421c の対象・依存先・metric 回帰は accepted、全て終了コード 0、キャッシュ保存失敗 0。詳細は benchmarks/records/complex-hilbert/README.md のチェックポイントを参照。

コンパクト作用素の和をコンパクト集合の積と加法の連続性で証明し、和の定理と零空間での例を個別検査した。次は前合成、ノルム極限、随伴、恒等作用素の有限次元性。

ソース commit bf8fcfd9 の対象 full-check-local と依存先検査は accepted、終了コード 0、キャッシュ保存失敗 0。詳細は benchmarks/records/complex-hilbert/README.md を参照。

コンパクト作用素の有界作用素との前合成を、単位球の像の正規化と相対コンパクト集合の連続像によって証明した。対象モジュールと零空間の例の個別検査は終了 0。次はノルム極限・随伴・恒等作用素の有限次元性と基礎補題。

完備距離空間の閉・全有界集合のコンパクト性と、全有界集合の閉包のコンパクト性を functional_analysis.Metric.Geometry.TotalBoundedCompact に追加した。有限ネットと既存の ultrafilter・既存の classicalIndefiniteChoice を使用し、新しい公理は追加していない。個別検査は終了 0。次はノルム極限のコンパクト性への適用、有限次元性と随伴。

完備値域でのコンパクト作用素のノルム極限を、単位球上一様の距離近似から全有界性を得て証明した。Compact.Limit と零空間の例は個別検査で終了 0。残りは随伴のコンパクト性、恒等作用素のコンパクト性から有限次元性、および有限次元・有限階数近似の基礎補題。

ソース commit 2584ef40 に対する対象・依存先・functional_analysis.Metric.Geometry の検査はいずれも accepted、終了 0、キャッシュ保存失敗 0。結果は benchmarks/records/complex-hilbert/README.md を参照。

有限集合が張る部分空間に向けて、既存の Hermitian.Inner.Of.Unit の階数 1 射影を複素 Hilbert 空間へ接続し、縮小性、有界作用素としての構成、有限自由座標を通る因子分解を Space.Hilbert.RankOne に追加した。個別検査は終了 0。次は有限生成集合への拡張、有限階数近似、随伴と恒等作用素の有限次元性。

有限階数自己随伴射影を有限集合の各元を固定するよう帰納的に拡大する構成を作業中。Extend.Nonzero の個別検査は成功したが、全体の最初の検査は import 解決エラーで失敗し修正中。検査対象は Space.Hilbert.FiniteProjection。長い検査はこの保存状態を push 後に再開する。
有限集合を固定する有限階数自己随伴射影の構成は修正後の個別検査で終了 0。有限ネットから有限階数近似を作る。
有限ネットを固定する有限階数射影を用い、任意のコンパクト作用素の単位球上一様な有限階数近似を Compact.Approximation.existsApproximation で証明した。対象モジュールの個別検査は終了 0。次は有限階数作用素のコンパクト性、随伴の有限階数性、恒等作用素への適用。

恒等作用素がコンパクトなら有限次元となることを Compact.Identity.finiteDimensional で証明した。有限次元は恒等写像が有限個の複素座標を通って因子分解するという明示的な線形 retract として定義する。有限ネットを固定する有限階数射影が恒等写像でなければ、直交する単位ベクトルの距離が 1 以上となる矛盾を利用する。対象と零空間の例の個別検査は終了 0。残りは有限階数作用素のコンパクト性と随伴による閉性。
