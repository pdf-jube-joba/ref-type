# B05 検査記録

検査対象 commit: `08599c12`。基点 main: `bd8fd86d5368968ff22e06f81beb5469bc348623`。
専用 worktree の `libs/refcache/` を利用し、300秒上限で実行した。

| 検査 | 結果 | 再検査 module | 再利用 module | ソースステップ |
| --- | --- | --- | --- | --- |
| 対象 `--full-check-local` | accepted | 4 | 421 | 19 |
| 依存込み通常検査 | accepted | 0 | 1396 | 0 |

依存込み検査の最初の実行は、実行中のソース変更を検出して中断された。
ソースを commit・push した後、対象・依存込みの順に再実行して上記の結果を得た。
グラフ座標、コンパクト性、普遍束、安定化、直和、直交補、射影空間と束の比較は未実装であり、それらの検査は未実行。

## 継続作業の検査

`80281272` の対象 `--full-check-local` は accepted、16 module・235 steps を再検査し543 module を再利用した。
同じ commit の workspace 全体の通常検査は300秒の時間上限で未完了、終了コード2。
対象依存閉包の `--module grassmannians` の通常検査は accepted、559 module を再利用しキャッシュ保存失敗は0。
グラフ表示の追加後は実モジュールの個別検査が accepted、複素側と全体の検査はまだ必要。
