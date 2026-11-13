# G23 独立レビューと復旧後のソース照合

2026-11-12 に独立レビュー担当が作成した。
復旧後のレビュー対象は `b52aa8afca2d251c845cd6580f32a15093dd088e` で、作業場所は `/workspace/shared/g23-current-main` である。
G23 の既存レビューはこのコミットの checker ソースにも適用でき、具体的な未解決の阻害指摘はない。
集約検査の完了を意味する判定ではない。

## 今回確認したソース

| 対象 | Git object ID |
| --- | --- |
| 対象コミット | `b52aa8afca2d251c845cd6580f32a15093dd088e` |
| 対象コミットの tree | `4a10089c02331f511d91dff56005483239872828` |
| `src` tree | `06c6742985407363110054c7266a6a85131e5805` |
| `tests` tree | `7d7b4e1c5563ec34292d24337172aca2ccc260d9` |
| `scripts` tree | `65d2c856336a5c4a0385be458f509cf941591471` |
| `Cargo.toml` blob | `e7e6488863e0e9e2ef188e504c52eb640be1cd8b` |
| `Cargo.lock` blob | `4cc71dabe22dc5bc04efcf037a8f5957dd50b68a` |
| `libs` tree | `fda10f6db37f287d0de47458b4f76d34eb34603f` |

`src`、`tests`、`scripts` と二つの Cargo ファイルは、以前にレビューした `3b1c4086a3784f0773f56ba97a53ba7121962347` と一致することを Git object ID と空の差分で確認した。
`libs` は統合元 main `d9da7c0ace28ecab2cc83e8dcfef9258ee0235b4` と一致する。
`3b1c4086a3` からのライブラリ差分は D01 の `bundle_connections`、その workspace 登録と一覧であり、checker に追加の変更はない。
G23 の capture 識別子、Program のカテゴリ判定、unifier、checkpoint の保存・復元を静的に再確認し、統合による新たな相互作用の問題は見つかっていない。

## 独立レビューで発見し、解消を確認した問題

1. **capture 内の lambda の束縛変数。**
   初期実装は内部の穴を直接共有し、複製した lambda の異なる `SymbolId` を共通文脈から除外したため、有効な入力を拒否した。
   capture の値全体を内部の共有 assignment で比較する実装に変更し、alpha 同値な束縛の下で制約を解けることを確認した。
   lambda の本体・型注釈、複数の内部束縛、転送の例で解消を確認した。
2. **Program の application head。**
   共有 wrapper を先に value と解釈すると、lambda や型注釈付きの computation が thunk として誤分類され、有効な application を拒否した。
   syntax/HIR の `ProgramFunctionExp::Assign` が元の head の分類を保持し、実際のカテゴリの判定後に共有する修正で解消した。
   lambda、型注釈付き関数、`cfun`、`force` を確認し、明示的な `force` を欠く thunk application の拒否も維持されていた。
3. **Blocked の合同比較と beta 簡約。**
   G23 の追加制約によって、入れ子の等式計算で既存 unifier の問題が顕在化した。
   簡約前の application の頭が一致せず Blocked になっても、外側の引数から得た暫定代入を保持していた。
   `MetaContext::unify_inner` で Blocked 時にも snapshot を戻してから簡約後の比較へ進む修正を確認した。
   3行の beta 簡約の例は baseline main でも失敗し、入れ子の等式計算は baseline で成功、G23 の修正前で失敗、最終修正で成功した。
   この比較により、既存の推論上の問題と G23 による顕在化を区別した。

## 以前の実行で観測した結果

次は環境再作成前の独立実行結果であり、今回の再実行結果ではない。
以前の `/tmp/g23-review` の手動再現例、CLI とログは現環境には残っていないため、本節はこのレビュー担当が保持する会話記録に基づく。

- 最終 checker を用いた手動19例はすべて期待どおりで、意図した拒否3例も維持されていた。
- macro inference と contextual inference の専用24ケースはすべて成功した。
- 最終レビュー対象は `19d76b4a37ec944c70a0dddcc3f2d5365a265640` で、検証 CLI の SHA-256 は `cb74a202907f039960058a9f262d975eb8b359f6f5b42fb8d7f7620e9521d23c` だった。
- 比較用 baseline は main `60c8e15517e7e6c7701edcf6fe20b7d5c60a7f00` で、CLI の SHA-256 は `2bea01edc0ecfb13f82c71acf48b58ee9b8a0d1bb664fb32266e63087dad039d` だった。
- 続く統合 `8d435794edd70c5471aeaf81fcfd4c6bb88a1485` の checker 差分は checkpoint の保存間隔で、保存内容・識別子の復元・検査順序への変更はなかった。
- `3b1c4086a3784f0773f56ba97a53ba7121962347` は、その保存間隔の式に対する rustfmt の整形だけで、評価内容が同一であることを静的に確認した。

## 今回の検証範囲と残る確認

今回実行したのは Git object ID の照合、差分の確認と上記 checker 箇所の静的レビューである。
復旧後のバイナリによる手動例、集約検査、Rust suite は本レビューでは実行していない。
以前の動的結果を復旧後の実行証拠として扱っていない。
現在の `libs` 全体に対する最終 checker の集約検査と、復旧後のビルド・テスト結果は統合担当の検証記録で確認する必要がある。
レビュー上の未解決指摘はないが、この記録単独では最新統合状態の実行検証完了を証明しない。
