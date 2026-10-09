# ホモロジー代数の証明付き計算

`homological-algebra.sh` は、拡張 Euclid の正負の入力と、整数行列の積・基本変形・対角化の利用例をキャッシュなしで検査する。
利用例は機械の実行結果を閉じた等式として検査し、一般の数学的仕様との対応証明にも適用する。
計測時の対角化の機械は同じ非対角行列から \(2,-4\) を、\(\operatorname{diag}(2,3)\) から整除を修正して \(1,-6\) を返す。
現在の `Smith.Diagonalize` は符号を正規化し、\(2,4\) と \(1,6\) を変換行列・逆行列とともに返す。
整数行列の積は \(\begin{pmatrix}2&4\\6&8\end{pmatrix}\begin{pmatrix}1&3\\0&1\end{pmatrix}=\begin{pmatrix}2&10\\6&26\end{pmatrix}\) である。

```sh
cargo build -p cli
benchmarks/homological-algebra.sh
```

出力先の既定値は `work/homological-algebra-benchmark` であり、第1引数で変更できる。
CSV は検査プロセス全体の経過時間と最大 RSS を記録する。
依存する宣言の検査時間も含むため、数値だけの実行時間とは分けて読む。

Rust 1.95.0 の debug CLI による 2026-10-08 の測定値は次の通りである。
CPU や同時実行する検査によって変動する。

| 利用例 | 経過時間 | 最大 RSS |
| --- | --- | --- |
| 拡張 Euclid | 7.648 秒 | 380768 KiB |
| 2×2 整数行列の積・対角化 | 42.843 秒 | 1188908 KiB |
