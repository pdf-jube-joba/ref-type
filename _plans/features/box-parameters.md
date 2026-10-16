<a id="g04"></a>

>  ## G04: Machine の実行を Box にする定義
>
>  Machine を引数に取り、その実行を Box にする共通の定義を書きたい。
>
>  ```text
>  \definition runBox(machine: Machine): \Box[machine.State ~> \F(machine.Output)] :=
>    \box[_](\force machine.run);
>  ```
>
>  現在は引数の State と Output が未確定なため、Box の閉性検査でこの定義を検査できない。
>  `std.Program.runBox` はマクロとして提供し、呼出側で具体化した Machine の実行を検査している。

[比較サンプル G04](../gaps.md#g04) を参照。

# Box の parameter と評価開始条件

Program の型・value parameter を Box に許す案を検討中。
現在は [型と payload を空文脈で検査](../../src/kernel/src/check.rs) し、payload の reflection も検査する。
[簡約](../../src/kernel/src/reduction.rs) は Box の内側でも進み、閉じた payload が簡約不能になると `\squash` で reflection へ移る。

## 未具体化と実行終了

閉性を緩めると、簡約不能な項が入力待ちなのか実行結果なのかを区別する必要がある。

```text
x : U(F Nat)
M := force x to y in return 0
```

`x` が未具体化なら Program は止まるが、reflection した \((\lambda y.0)\bar x\) は Set 側で直ちに \(0\) になる。
先に `x := thunk N` を代入すれば、Program は `N` を実行してから `0` を返す。
reflection と具体化の順序が実行に影響する。

## 具体化を待つ案

Box の形成には parameter を許し、取り出しを環境の具体化まで保留する。
ただし、待つべき環境の範囲と Program / reflection の文脈対応は未決定である。

```text
return (thunk (force x))
```

この項は `x` が未具体化でも return の形にある。
全 parameter を待つ条件と、現在の実行に必要な入力だけを待つ条件を区別して検討する。
型・value の代入、外側の beta 簡約、Box 内の簡約、reflection の順序と停止性を合わせて定める。
