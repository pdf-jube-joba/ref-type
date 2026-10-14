# 局所文脈を持つ関数の推論

## contextual argument

definition 内部の lambda 注釈を推論してから、関数を module 引数として渡せる。

```toml case
id = "contextual_inference.contextual-argument"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
  \structure Carrier { A: \Set, }
  \definition identity(C: Carrier): C.A -> C.A := \fun (x: _) => x;
  \module Pass(A: \Set, f: A -> A) { \definition value: A -> A := f; }
  \inductive Unit: \Set := | unit: Unit;
  \definition C: Carrier := Carrier { A := Unit };
  \import \root.Repro[].Pass[A := C.A, f := identity C] \as P;
  \definition value: Unit -> Unit := P.value;
}
```

## bound argument

型を付けて束縛した関数値も、module の引数として渡せる。

```toml case
id = "contextual_inference.bound-argument"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Repro {
  \structure Carrier { A: \Set, }
  \definition identity(C: Carrier): C.A -> C.A := \fun (x: _) => x;
  \module Pass(A: \Set, f: A -> A) { \definition value: A -> A := f; }
  \inductive Unit: \Set := | unit: Unit;
  \definition C: Carrier := Carrier { A := Unit };
  \definition bound: C.A -> C.A := identity C;
  \import \root.Repro[].Pass[A := C.A, f := bound] \as P;
  \definition value: Unit -> Unit := P.value;
}
```

## contextual inference

関数を引数に取る application の期待型から、内側の lambda の型を推論できる。

```toml case
id = "contextual_inference.contextual-inference"
scope = "module"
expect = "accept"
name = "Repro"
parameters = '''A: \Set'''
```

```ref
\macro congr($A, $B) :=
  (\fun (law: \forall (f: $A -> $B) -> \forall (a, b: $A) -> a = b -> f a = f b) => law)
(\fun (f: $A -> $B) => \fun (a, b: $A) => \fun (e: a = b) =>
\idelim a = b \with x: $A => f a = f x \by { base: \refl(f a), equality: e });

\definition identity(n: A): A := n;
\definition mapping: A -> A := \fun (n: A) => n;
\definition End: \Set := A -> A;
\definition matches(n: A): identity (mapping n) = identity (mapping n) :=
  congr!{End A} (\fun (f: _) => identity (f n)) _ _ (\refl(mapping));
```

## infer projection

期待する record の型から binder の穴を埋め、その field を射影できる。

```toml case
id = "inference_and_constructor_aliases.infer-projection"
scope = "module"
expect = "accept"
name = "Repro"
```

```ref
\structure And[P, Q: \Prop]: \Prop { left: P, right: Q, }
\definition andElim(P, Q, R: \Prop): (P -> Q -> R) -> And[P, Q] -> R :=
  \fun (curried: _) (value: _) => curried (value #left) (value #right);
```

## infer take continuation

exists を除去した witness を使う後続の関数の型も、期待型から推論できる。

```toml case
id = "inference_and_constructor_aliases.infer-take-continuation"
scope = "module"
expect = "accept"
name = "InferTake"
parameters = '''A: \Set, P: \Prop'''
```

```ref
\definition elim: (\exists A) -> (A -> P) -> P :=
  \fun (e: _) (step: _) => \block {
  \takefrom x: A \by e \then
  \return step x
};
```

## infer subset

subset の期待型から binder を推論し、基底型の関数と membership の証明で利用できる。

```toml case
id = "inference_and_constructor_aliases.infer-subset"
scope = "module"
expect = "accept"
name = "InferSubset"
parameters = '''A: \Set, P: A -> \Prop, f: A -> A'''
```

```ref
\definition Parameter: \Set := \Cast[A] ({ x: A \where P x });
\definition apply: Parameter -> A := \fun (t: _) => f t;
\definition property: \forall (t: Parameter) -> P t :=
  \fun (t: _) => (\fun (unused: A) => \bysub(A, Parameter, t)) (f t);
```

## contextual applications refine function types with repeated arguments

同じ引数を繰り返す application でも、期待型から関数引数の型を推論できる。

```toml case
id = "contextual_applications_refine_function_types_with_repeated_arguments"
scope = "module"
expect = "accept"
name = "Repro"
parameters = '''A: \Set'''
```

```ref
\macro congr($A, $B) :=
  (\fun (law: \forall (f: $A -> $B) -> \forall (a, b: $A) -> a = b -> f a = f b) => law)
(\fun (f: $A -> $B) => \fun (a, b: $A) => \fun (e: a = b) =>
\idelim a = b \with x: $A => f a = f x \by { base: \refl(f a), equality: e });
\definition identity(n: A): A := n;
\definition mapping: A -> A -> A := \fun (n, m: A) => n;
\definition Binary: \Set := A -> A -> A;
\definition matches(n: A): identity (mapping n n) = identity (mapping n n) :=
  congr!{Binary A} (\fun (f: _) => identity (f n n)) _ _ (\refl(mapping));
```

## imported front definitions still check argument types

推論した関数を別の帰納型の関数として渡しているため拒否される。

```toml case
id = "imported_front_definitions_still_check_argument_types"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Repro {
  \structure Carrier { A: \Set, }
  \definition identity(C: Carrier): C.A -> C.A := \fun (x: _) => x;
  \inductive Unit: \Set := | unit: Unit;
  \inductive Other: \Set := | other: Other;
  \definition C: Carrier := Carrier { A := Unit };
  \module Pass(f: Other -> Other) {}
  \import \root.Repro[].Pass[f := identity C] \as P;
}
```

## wrong inferred proof

P の証明を Q の証明として返しているため拒否される。

```toml case
id = "wrong-inferred-proof"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''P, Q: \Prop'''
```

```ref
\definition bad: P -> Q := \fun (p: _) => p;
```

## escaping inferred witness

exists から取り出した witness が結果へ逃げるため拒否される。

```toml case
id = "escaping-inferred-witness"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \Set'''
```

```ref
\definition bad: (\exists A) -> A := \fun (e: _) => \block { \takefrom x: A \by e \then \return x };
```

## unproved inferred subset

基底型の値を membership の証明なしに subset の値として返すため拒否される。

```toml case
id = "unproved-inferred-subset"
scope = "module"
expect = "reject"
name = "Wrong"
parameters = '''A: \Set, P: A -> \Prop'''
```

```ref
\definition Sub: \Set := \Cast[A] ({ x: A \where P x }); \definition bad: A -> Sub := \fun (x: _) => x;
```

## module 引数 / hole

module の引数に直接推論の穴を書いているため拒否される。

```toml case
id = "module-argument-hole"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Repro { \inductive Unit: \Set := | unit: Unit; \module Pass(f: Unit -> Unit) {} \import \root.Repro[].Pass[f := _] \as P; }
```

## module 引数 / lambda-hole

module の引数に直接推論の穴を書いているため拒否される。

```toml case
id = "module-argument-lambda-hole"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Repro { \inductive Unit: \Set := | unit: Unit; \module Pass(f: Unit -> Unit) {} \import \root.Repro[].Pass[f := \fun (x: _) => x] \as P; }
```
