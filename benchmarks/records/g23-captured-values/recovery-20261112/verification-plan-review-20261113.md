# 残り対象の検査計画に対する独立レビュー

2026-11-13 に、checker や Cargo テストを起動せず、計画・元レポート・ソースの対応を独立に確認した。
レビュー時の HEAD は `c5e30568866a73b9a4aa7541dcdaf85bcfbf8ba3` である。
計画に具体的な検証の弱体化や阻害指摘は見つかっていない。
この判定は集約検査の完了を意味しない。

## 同一性と既存の checker レビュー

- `src` tree は `06c6742985407363110054c7266a6a85131e5805`、`libs` tree は `fda10f6db37f287d0de47458b4f76d34eb34603f` だった。
- 既レビューの `3b1c4086a3784f0773f56ba97a53ba7121962347` から `src`、`tests`、`scripts`、Cargo ファイルに差分がなく、既存の checker レビューは適用できる。
- 使用予定の checker の SHA-256 は `cc0578470d23ba582931b065f1f1a68e9afe64068bf4e24e0a050f73eeb1845c` で、実ファイルと build manifest の198入力ファイルの digest を照合した。
- `full` と `full-16g` の元 snapshot の SHA-256 はともに `649639ff1e32582d88b616f34e20b90f52c61cde41229aaf6836016b959aeffe` だった。
- `critical/source.json` の SHA-256 は `2e3c5a7d60d640e173b4c7e825eb5f55bcf40cef5856f6e0f1ead7e28a7bfe28` だった。
  entry を除いた全データの正規化 JSON digest は full と critical で一致し、両方とも13,179ファイルを含むことを独立に確認した。

## 元レポートからの被覆の再計算

`/workspace/shared/g23-recovery/full/` の元 driver report は全体として失敗しているため、全体の合格として扱っていない。
exit code 0 かつ accepted の個別レポートだけを読み、各要求範囲が実際の `verified_modules` に含まれ、保存失敗・破損読み取りが0であることを確認した。

| 証拠 | 確認した被覆 |
| --- | ---: |
| full の accepted 132範囲の和集合 | 13,854 |
| critical の accepted report 全体 | 3,312 |
| critical が full に追加する対象 | 562 |
| 和集合 | 14,416 |
| 対象一覧との差集合 | 70 |
| 全対象 | 14,486 |

`critical/execution.json` は exit code 0、元 report は accepted で、`k_theory_thom.Thom.Complexification.Compact.Isomorphism` を含む。
計画に挙げられた133個の seed report の digest はすべて元ファイルと一致した。
`coverage-union-observation.json` と `remaining/plan.json` の和集合・差集合は独立の再計算と一致し、残り70対象はすべて `k_theory_thom` に属する。
レビュー時の `full-16g` の accepted 13,807対象は full の13,854対象の部分集合だった。
実行中 worker の途中到達位置や CPU 時間は accepted 被覆に算入していない。

## helper と最終検査の評価

レビューした `prepare_remaining.py` の SHA-256 は `1ceabd1d9f1dac9b7d3437f3a22311b08f5c5bbbd06d0452fcae985b5df882b9` である。
helper は snapshot と checkout・Git・build 入力を照合し、既存 accepted レポートを計画上の seed として扱う。
未被覆の対象は同じバイナリと完全な snapshot を使い、entry だけを package に変更した通常の `--module-only` 検査を行う。
`--parse-only` や検査省略用の設定はなく、CLI の正常終了・accepted・対象の被覆・保存失敗0・破損読み取り0を要求する。
独自 state lock に加えて `full-16g/lock` を保持するため、現在の driver が終了して lock を解放する前には実行段階へ進まない。
子プロセスの終了時 signal、親消失時の停止と finally の cleanup も確認した。

標準 `scripts/check_all.py` の実ファイル digest は、元の二つの driver report に記録された `b0b7159aa8440dd12d090fdb29cc61df4d7db29c8e58b11c335e8126b7e9ef9f` と一致する。
標準 driver は今回の seed 被覆を合格結果として取り込まず、通常の CLI による全要求範囲の確認を行い、最後に source と対象一覧を再列挙して一致と完全被覆を要求する。
したがって helper の `prewarm-complete` は最終合格の代わりにならない。

元 report と checkpoint を保存して現在の重複した広い検査を終了し、残り対象を通常キャッシュで準備した後、未変更の標準 driver で現行 source・同一 checker に対する14,486対象の accepted を取得する計画は妥当である。
被覆の和集合だけでは、最新の全体合格や今後のメモリ条件での完走は証明されない。
最終の source 一致・完全被覆・正常終了の確認が未完了であり、統合判断にはその実行結果が必要である。

このレビューでは既存 worker、checker、キャッシュ、ソースを変更せず、重複した実行検証は起動していない。
