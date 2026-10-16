<a id="g04"></a>

# Box の parameter と残余項の reflection

実装済み。
Box の型・payload は型と value の parameter を持てる。
形成時には現在の文脈で Program の typing と reflection の typing を検査する。

```text
\definition runBox(machine: Machine): \Box[machine.State ~> \F(machine.Output)] :=
  \box[_](\force machine.run);
```

`std.Program.runBox` は通常の定義として提供する。
[比較サンプル G04](../gaps.md#g04) は引数を取る定義と具体値を使う定義の両方を検査できる。

## 評価と具体化

`\squash` は Program の評価位置に従って payload を簡約し、次の Program step がなくなった残余項を Logic に反映する。

```text
x : U(F A)
a : A
M := force x to y in return a
```

`x` が未具体化なら Program は入力待ちになり、reflection した \((\lambda y.\bar a)\bar x\) は Logic 側で \(\bar a\) になる。
具体化が先ならその入力で Program の簡約を進める。
両経路の整合性は、[Box 消去](../../doc/book/src/props/box_elimination.md) の Rf-step と Rf-subst で扱う。
Program step が無限に続く場合には、この条件による reflection への移行は起こらない。

```text
return (thunk (force x))
```

この残余項も reflection に移り、Logic 側では \(\bar x\) になる。
定義の capture は元の Program parameter を保持し、Logic 側の参照で reflection を行う。
namespace の具体化では Box の型・payload と反映された参照の双方に代入する。

仕様は [system.md](../../doc/book/src/system.md)、受理例は [Box の parameter と残余項](../../tests/language/program/box-parameters.md) にある。
