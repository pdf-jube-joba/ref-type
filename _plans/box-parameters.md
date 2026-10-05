>  ## Machine の実行を Box にする定義
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

# Box の parameter と評価開始条件

## 検討状況

`\Box` に Program の型 parameter・value parameter を許すための論点整理。
parameter の具体化、Box 内の簡約、`\Force` による reflection の関係が未決定であり、実装方針は検討中である。

## 動機と現状

[Machine の実行を Box にする定義](gaps.md#machine-の実行を-box-にする定義)では、引数に依存する Program の型と項を Box に入れたい。
必要になるのは structure の中の Program 部分であり、Set の一般の項を Program の value として受け入れることとは別の問題である。

[現在の体系](../doc/book/src/system.md)では、Box の computation type と payload を空文脈で型検査する。
[kernel の型検査](../src/kernel/src/check.rs)でも、payload の自由変数と module parameter を閉性検査で制限している。
box intro では payload の reflection についても型検査するため、開いた Box の検討には反映先の文脈も関わる。

現在の box step は payload の Program 簡約を Box の内側で進める。
`\Force` は閉じた payload がこれ以上簡約できなくなったところで reflection に移す。
[kernel の簡約](../src/kernel/src/reduction.rs)にも `BoxProgram` 自体を一段進める処理がある。
したがって、現状の規則では `\Force` だけを Program の実行開始点とみなす説明には調整が必要になる。

## parameter を実行前の環境とみなす考え方

module parameter は Program の実行より前に代入されるものとして理解できそうである。
Program の型 parameter と value parameter についても、実行前に環境から与えられるという見方が候補になる。

Program を \(M\)、具体化する環境を \(\rho\) とすれば、実行対象を \(M[\rho]\) と考える。
型変数には Program の型を、value 変数には Program の value を代入する。
この分類が保たれるなら、自由変数を含むこと自体は value/computation の区別と両立しそうである。
`thunk N` が value として渡される場合も、`N` の実行位置は Program 内の `force` によって決まる。

型検査時の `x: A` は入力の分類を与え、実行時の `x := V` は具体的な入力を与える。
`match x ...` は実行前に環境で既定された value を参照している、と理解できる。
この説明を採用する場合、環境の具体化をどの段階で要求するかが課題になる。

通常の `\definition` も名前を介して項を供給する点では parameter に似ている。
本体が既に存在する定義と、将来具体化される parameter の違いはあるが、定義の展開と Program の評価順序の関係には整理の余地がある。

## 未具体化による停止と実行終了

閉性を緩めると、「これ以上簡約できない」が実行終了を意味するとは限らなくなる。
以下は core の操作を表す模式例である。

```text
x : U(F Nat)
M := force x to y in return 0
```

`x` が未具体化なら `force x` が止まり、`M` 全体も進めなくなる。
ここで簡約不能だけを条件に reflection を許すと、現在の reflection の式から Set 側には概ね次が現れる。

\[
(\lambda y.\,0)\,\bar x
\]

Set 側の beta 簡約では、この式は直ちに \(0\) になる。
一方、先に `x := thunk N` を代入すると、Program は次になる。

```text
N to y in return 0
```

こちらは `N` を実行してから `0` を返す。
停止する `N` でも、reflection と具体化の順番によって、Program として実行される計算が異なりうる。
この例は結果の不一致や体系の矛盾を示すものではなく、Program の評価順序をどこまで保証したいかを問うものである。

また、開いた項の簡約不能性は代入によって失われうる。
未具体化の項を扱う `\Force` の条件には、入力待ちと実行結果の区別が必要になる。

## 具体化を待つ案と残る疑問

Box の形成には parameter を許し、`\Force` による取り出しを環境の具体化まで保留する案が出た。
ただし、「環境が具体化した時点」をどう定義するかは未解決である。

議論中の次の式は、外側の beta 簡約と Box の取り出しの順序を表す模式例である。
ここでの `\squash` は、議論中の Box の取り出しを表す記法である。

```text
(\fun (x:A) => \squash \box (M)) 1
```

まず次の形になってから squash が始まってほしい、という直感がある。

```text
\squash \box (M[x := 1])
```

ただし、この例を書いた時点で、その説明自体にも違和感が残った。
外側の適用を先に進めること、payload が閉じること、実行に必要な入力が得られることのうち、どれを本質的な条件とするかは検討中である。
この例での `x` の分類と Box 内での参照方法も、具体的な型規則とともに定める必要がある。

全 parameter の具体化を要求する条件は、実行に必要な入力だけを待つ条件より強い可能性がある。
例えば次は、`x` が未具体化でも外側の computation としては return の形になっている。

```text
return (thunk (force x))
```

関数や thunk の内部に残る parameter と、現在の実行を止めている parameter の扱いが論点になる。
開いた実行結果を取り出せるようにする場合は、Program の文脈と reflection 先の文脈の対応も必要になる。

## 次に整理する点

- 制御したい順序の範囲：Program 内の実行順序と、外側の代入・定義展開・Set の簡約との関係。
- module parameter の具体化と、binder による自由変数への代入の共通点・相違点。
- Box 内の簡約を進める条件と、`\Force` で reflection に移る条件。
- 未具体化の `\Force` を含む定義の型検査と等価性判定。
- Program の文脈・代入と、それらの reflection の対応。
- parameter を持つ payload の reflection の型検査と、既存の停止性に関わる条件の扱い。

現段階では、parameter を許す方向に可能性があるという見立てと、具体化待ちをどのように規則化するかという未決定の問題が残っている。
