# 特異鎖の cap 積

`Integral[A, source].At[p, q]` は整数係数の余鎖を、特異 \((p+q)\)-鎖から \(p\)-鎖への線形写像に対応させる。
単体の前半を出力し、後半で評価した余鎖の値を係数とする。

`map beta` は整数線形写像であり、`onGenerator beta sigma` は単体上の値を与える。

```sh
target/debug/cli libs/topology/singular/cap --module singular_cap.Integral.At --diagnostics compact
```
