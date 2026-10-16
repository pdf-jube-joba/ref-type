# binder と局所定義

## structure 引数と局所 scope

structure の field を局所 binder と subset の定義から使い、同じ値に簡約できる。

```toml case
id = "shared_definitions_preserve_subset_and_local_scopes"
scope = "module"
expect = "accept"
name = "Sharing"
```

```ref
\structure Bundle { Carrier: \Set, seed: Carrier }
\definition identity(B: Bundle)(x: B.Carrier): B.Carrier := x;
\definition Fixed(B: Bundle): \Pow B.Carrier :=
  { b: B.Carrier \where identity B b = b };
\inductive Unit: \Set := | unit: Unit;
\definition bundle: Bundle := Bundle { Carrier := Unit, seed := Unit::unit };
\definition delayed: Unit -> Unit := \fun (_: _) => bundle.seed;
\definition delayedLaw: delayed Unit::unit = Unit::unit := \refl(Unit::unit);
\definition local(B: Bundle)(x: B.Carrier)(unused: x = x): B.Carrier := identity B x;
\definition localLaw(B: Bundle)(x: B.Carrier): local B x (\refl(x)) = x := \refl(x);
```

## block 内の関数

保存した値は後続の同名 binder に捕捉されず、直接書いた関数と一致する。

```toml case
id = "logical_block_fun_preserves_binder_order_and_scope"
scope = "module"
expect = "accept"
name = "BlockFunctions"
parameters = '''A: \Set, P: A -> \Set'''
```

```ref
\definition direct: \forall (x, y: A) (h: P x) -> A -> P x :=
  \fun (x, y: A) (h: P x) (z: A) => h;
\definition blocked: \forall (x, y: A) (h: P x) -> A -> P x := \block {
  \fun (x, y: A) (h: P x) \then
  \let saved: P x := h \then
  \fun (x: A) \then
  \return saved
};
\definition same: blocked = direct := \refl(direct);
```

## let の展開と shadowing

let の値と型 alias は透過的に展開され、入れ子や同名 binder を経ても元の参照を保つ。

```toml case
id = "logical_let_definitions_are_transparent_and_capture_avoiding"
scope = "module"
expect = "accept"
name = "LocalDefinitions"
parameters = '''A: \Set, a: A'''
```

```ref
\macro equality($x, $y) := $x = $y;
\definition simple: a = a := \block {
  \let x: A := a \then
  \let h: x = a := \refl(a) \then
  \return h
};
\definition nested: \forall (x: A) -> \forall (y: A) -> x = x :=
  \fun (x: A) => \block {
  \let saved: A := x \then
  \let alias: A := saved \then
  \fun (x: A) \then
  \let x: A := alias \then
  \let h: equality!{x saved} := \refl(saved) \then
  \return h
};
\definition shadowed: \forall (x: A) -> x = x := \block {
  \let x: A := a \then
  \return \fun (x: A) => \refl(x)
};
\definition restored: a = a := \block {
  \let x: A := a \then
  \let f: A -> A := \fun (x: A) => \block {
    \let x: A := x \then
    \return x
  } \then
  \return \refl(f x)
};
\definition inferred: a = a := \block {
  \let x: _ := a \then
  \let h: x = a := \refl(x) \then
  \return h
};
\definition inferred_later: a = a := \block {
  \let x: A := _ \then
  \let h: x = a := \refl(a) \then
  \return h
};
\definition type_alias: a = a := \block {
  \let T: \Set := A \then
  \let x: T := a \then
  \let P: \Prop := x = a \then
  \let h: P := \refl(a) \then
  \return h
};
\definition unused_proof: A := \block {
  \let h: a = a := \refl(a) \then
  \return a
};
```

## enough の後の目標

P から Q への含意を渡した後は P を証明すれば Q の証明になる。

```toml case
id = "logical_enough_changes_the_remaining_goal"
scope = "module"
expect = "accept"
name = "Enough"
parameters = '''P, Q: \Prop, p: P, implication: P -> Q'''
```

```ref
\definition result: Q := \block {
  \enough P \by { implication } \then
  \return p
};
```

## let の型注釈

let の型注釈によって x は基底型 A の値になるため、membership の証明なしに subset の値として返すと拒否される。

```toml case
id = "logical_let_preserves_the_declared_type"
scope = "module"
expect = "reject"
name = "LocalAnnotation"
parameters = '''A: \Set, S: \Pow (A), s: \Cast[A] (S)'''
```

```ref
\definition invalid: \Cast[A] (S) := \block {
  \let x: A := s \then
  \return x
};
```

## まとめた product binder

p、q、r はいずれも外側の P の証明として束縛される。

```toml case
id = "grouped_product_binders_keep_the_outer_type"
scope = "module"
expect = "accept"
name = "Grouped"
```

```ref
\definition last: \forall (P: \Prop) -> \forall (p, q, r: P) -> P :=
  \fun (P: \Prop) => \fun (p: P) => \fun (q: P) => \fun (r: P) => r;
```

## まとめた lambda binder

同じ宣言の binder 群は、同名の P を束縛する前の型注釈を共有する。

```toml case
id = "grouped_lambda_binders_keep_the_outer_type"
scope = "module"
expect = "accept"
name = "Grouped"
```

```ref
\definition last: \forall (P: \Prop) -> P -> P -> P -> P :=
  \fun (P: \Prop) => \fun (p, q, r: P) => r;
\definition shadowed: \forall (P: \Prop) -> P -> P -> P :=
  \fun (P: \Prop) => \fun (P, p: P) => p;
```

## まとめた宣言引数

帰納型の x、y、z の型は、同じ外側の A である。

```toml case
id = "grouped_declaration_binders_keep_the_outer_type"
scope = "module"
expect = "accept"
name = "Grouped"
```

```ref
\inductive Witness[A: \Set, x, y, z: A]: \Prop :=
  | intro: Witness
;
```

## membership と Cast の関数値

membership と Cast を関数として名前に束縛し、subset に適用できる。

```toml case
id = "membership_and_cast_are_first_class_functions"
scope = "module"
expect = "accept"
name = "SetOperators"
parameters = '''A: \Set, subset: \Pow A'''
```

```ref
\definition membership: \Pow A -> A -> \Prop := \In[A];
\definition cast: \Pow A -> \Set := \Cast[A];
\definition Specialized: \Set := cast subset;
```

## 使用しない let / 1

集合の値を要求する位置に命題の証明を渡している。結果で使わない定義も検査する。

```toml case
id = "unused-let-0"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: A := p \then \return \refl(a) };
```

## 使用しない let / 2

命題の証明を要求する位置に集合の値を渡している。結果で使わない定義も検査する。

```toml case
id = "unused-let-1"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: P := a \then \return \refl(a) };
```

## 使用しない let / 3

型と値を決める制約がない。結果で使わない定義も検査する。

```toml case
id = "unused-let-2"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: _ := _ \then \return \refl(a) };
```

## 使用しない let / 4

まだ束縛されていない自分自身を参照している。結果で使わない定義も検査する。

```toml case
id = "unused-let-3"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set, a: A, P: \Prop, p: P'''
```

```ref
\definition example: a = a := \block { \let unused: A := unused \then \return \refl(a) };
```
