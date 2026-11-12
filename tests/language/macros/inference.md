# macros / inference

## 等式消去の capture に渡す穴

等式の両端、束縛下の motive、基底に現れる同じ capture の穴を、等式の証明から推論する。

```toml case
id = "accept-macros.captured_hole_equality_elimination"
scope = "module"
expect = "accept"
parameters = '''A, B: \Set'''
```

```ref
\macro map_eq($f, $a, $b, $same) :=
  \idelim $a = $b \with x: A => $f $a = $f x
    \by { base: \refl($f $a), equality: $same };
\definition law[f: A -> B][a, b: A][same: a = b]: f a = f b :=
  map_eq!{f _ _ same};
```

## 再帰的なマクロ展開での等式消去

列の capture と token match を通じて渡した穴も、motive と基底の間で共有する。

```toml case
id = "accept-macros.forwarded_captured_hole"
scope = "module"
expect = "accept"
parameters = '''A, B: \Set'''
```

```ref
\macro map_eq($f, $a, $b, $same) :=
  \idelim $a = $b \with x: A => $f $a = $f x
    \by { base: \refl($f $a), equality: $same };
\macro forward(..args) := \tmatch args {
  | ($f, $a, $b, $same) => map_eq!{$f $a $b $same}
};
\definition law[f: A -> B][a, b: A][same: a = b]: f a = f b :=
  forward!{f _ _ same};
```

## 一つの穴に対する矛盾した制約

同じ capture の穴を二つの異なる局所変数として解くことはできない。

```toml case
id = "reject-macros.captured_hole_inconsistent_constraints"
scope = "module"
expect = "reject"
parameters = '''A: \Set, a, b: A'''
```

```ref
\macro duplicate($x) := \fun (h: $x = a) => \refl($x);
\definition impossible: (a = a) -> b = b := duplicate!{_};
```

## 別の呼び出しと名前付き穴

一つの宣言内で別々に呼び出すマクロの穴と、明示した名前付き穴は、それぞれの期待型から解く。

```toml case
id = "accept-macros.captured_hole_independent_calls"
scope = "module"
expect = "accept"
parameters = '''A: \Set, a, b: A'''
```

```ref
\structure Both: \Prop := {
  left: a = a,
  right: b = b,
  named: b = b,
};
\macro infer($x) := \refl($x);
\definition independent: Both := Both {
  left := infer!{_},
  right := infer!{_},
  named := \refl(_0),
};
```

## capture 内部の束縛変数

複製された lambda は内部の変数名の同一性ではなく、束縛の下で式全体を比較する。

```toml case
id = "accept-macros.captured_lambda_body_hole"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\definition identity: A -> A := \fun (x: A) => x;
\macro copy($f) := \fun (h: $f = identity) => \refl($f);
\definition law: (identity = identity) -> identity = identity :=
  copy!{{\fun (x: A) => _}};
```

## 複数の内部束縛と転送

型注釈と本体の穴を持つ lambda を転送しても、複製した関数の値が一致する。

```toml case
id = "accept-macros.forwarded_captured_nested_lambda"
scope = "module"
expect = "accept"
parameters = '''A: \Set'''
```

```ref
\definition first: A -> A -> A := \fun (x, y: A) => x;
\macro copy($f) := \fun (h: $f = first) => \refl($f);
\macro forward(..args) := \tmatch args { | ($f) => copy!{$f} };
\definition law: (first = first) -> first = first :=
  forward!{{\fun (x: _) => \fun (y: _) => _}};
```

## Program の capture と期待型

capture の共有によって、Program 関数の型注釈に期待型を伝える推論を妨げない。

```toml case
id = "accept-macros.program_capture_expected_function"
scope = "module"
expect = "accept"
```

```ref
\inductive Bool: \VType := | false: Bool | true: Bool;
\macro keep($x) := $x;
\definition identity: Bool -> Bool := keep!{{\fun (x: _) => \return(x)}};
\definition value: Bool := keep!{{Bool::true \of _}};
```

## Program の application head

capture を共有しても、lambda と型注釈を付けた computation は明示的な force を要求する value に変わらない。

```toml case
id = "accept-macros.program_capture_application_head"
scope = "module"
expect = "accept"
parameters = '''A: \VType, a: A'''
```

```ref
\definition identity: A -> A := \fun (x: A) => \return(x);
\macro call($f) := $f a;
\definition lambda: \F(A) := call!{{\fun (x: _) => \return(x)}};
\definition ascribed: \F(A) := call!{{identity \of _}};
\definition computationLambda: \F(A) := call!{{\cfun (x: _) => \return(x)}};
\definition forced: \F(A) := call!{{\force(\thunk(\fun (x: _) => \return(x)))}};
```

## Program の型と値の capture

型・computation type・value・computation の各位置で期待型と共有値を照合する。

```toml case
id = "accept-macros.program_capture_categories"
scope = "module"
expect = "accept"
parameters = '''A: \VType, a: A'''
```

```ref
\macro keep($x) := $x;
\check a: keep!{_};
\check \return(a): keep!{{\F(_)}};
\definition value: A := keep!{{a \of _}};
\definition computation: \F(A) := keep!{{\return(a \of _)}};
```
