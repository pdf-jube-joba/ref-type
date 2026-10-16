# Box の parameter と残余項

## 型と value の module parameter

Program の簡約で入力待ちになった項を反映し、Logic の beta 簡約で不要な入力を消去する。
return 内の thunk に残る parameter も反映する。

```toml case
id = "box-parameters.module"
scope = "module"
parameters = 'A: \VType, a: A, x: \U(\F(A))'
expect = "accept"
```

```ref
\definition boxed: \Box[\F(A)] := \box[_](
  \bind y: A <- \force x \in \return a);
\definition result: \squash[_](boxed) = a^ := \refl(a^);
\definition delayed: \Box[\F(\U(\F(A)))] :=
  \box[_](\return (\thunk (\force x)));
\definition delayedResult: \squash[_](delayed) = x^ := \refl(x^);
\definition identity: \Box[A ~> \F(A)] :=
  \box[_](\cfun (v: A) => \return v);
\definition application:
  \squash[_](\boxapp(identity, \box[_](\return a))) = a^ := \refl(a^);
```

## 定義の引数と具体化

通常の定義が型と value を受け取って Box を作る。
具体化の前後で reflection と代入の結果が一致する。

```toml case
id = "box-parameters.definition"
scope = "module"
expect = "accept"
```

```ref
\inductive Bit: \VType := | zero: Bit | one: Bit;
\definition package[A: \VType][a: A][x: \U(\F(A))]: \Box[\F(A)] :=
  \box[_](\bind y: A <- \force x \in \return a);
\definition residual[A: \VType][a: A][x: \U(\F(A))]:
  \squash[_](package A a x) = a^ := \refl(a^);
\definition concrete:
  \squash[_](package Bit Bit::one (\thunk (\return Bit::zero))) = Bit^::one :=
  residual Bit Bit::one (\thunk (\return Bit::zero));
\definition reflected[A: \VType][a: A]: A^ :=
  \squash[_](\box[_](\return a));
\definition substituted: reflected Bit Bit::one = Bit^::one := \refl(Bit^::one);
```

## namespace の具体化とキャッシュ

Box を公開する module を二つの値で具体化し、保存した検査結果も再利用する。

```toml scenario
id = "box-parameters.namespace-cache"
scope = "package"
```

```ref file=src/root.ref
\module Holder(A: \VType, boxed: \Box[\F(A)]) {
  \definition result: A^ := \squash[_](boxed);
}
\module Source(A: \VType, a: A, x: \U(\F(A))) {
  \definition boxed: \Box[\F(A)] :=
    \box[_](\bind y: A <- \force x \in \return a);
  \definition result: \squash[_](boxed) = a^ := \refl(a^);
  \import \root.Holder[A := A, boxed := boxed] \as Forward;
  \definition forwarded: Forward.result = a^ := \refl(a^);
}
\module Consumer {
  \inductive Bit: \VType := | zero: Bit | one: Bit;
  \import \root.Source[A := Bit, a := Bit::zero, x := \thunk (\return Bit::one)] \as Zero;
  \import \root.Source[A := Bit, a := Bit::one, x := \thunk (\return Bit::zero)] \as One;
  \definition zero: \squash[_](Zero.boxed) = Bit^::zero := Zero.result;
  \definition one: \squash[_](One.boxed) = Bit^::one := One.result;
  \definition forwarded: Bit^::one = Bit^::one := One.forwarded;
}
```

```toml step
id = "cold"
expect = "accept"
cache = "unused"
```

```toml step
id = "warm"
expect = "accept"
cache = "reused"
```

## 停止性証明内の Box

Program の定義を反映するとき、停止性証明が参照する parameter と Box も Logic の文脈に移る。

```toml case
id = "box-parameters.termination-proof"
scope = "module"
parameters = 'A: \VType, a: A'
expect = "accept"
```

```ref
\definition step: \U(A ~> \F(\RunStep[A, A])) :=
  \thunk (\cfun (s: A) => \return (\finish[A, A](a)));
\definition Terminates[s: A^]: \Prop :=
  \forall (P: A^ -> \Prop) ->
    (\forall (x: A^) ->
      (\step-match t: \RunStep[A^, A^] \return \Prop \with {
        | \continue next: P next
        | \finish output: \forall (Q: \Prop) -> Q -> Q
      }) (step^ x) -> P x) -> P s;
\definition terminates: Terminates a^ :=
  \fun (P: _) (h: _) =>
    h (\squash[_](\box[_](\return a))) (\fun (Q: \Prop) (q: Q) => q);
\definition result: \F(A) := \run[A, A](step, a) \by { terminates };
\definition reflectedResult: result^ = a^ := \refl(a^);
```
