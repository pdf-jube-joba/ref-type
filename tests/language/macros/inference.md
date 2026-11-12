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
