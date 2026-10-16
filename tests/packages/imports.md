# packages / imports

## packages resolve temporary module expressions

外部依存と同じ package の module の具体化は、同じ型引数を代入した carrier として利用できる。

```toml case
id = "packages_resolve_temporary_module_expressions"
scope = "package"
expect = "accept"
entry = "main"
```

```toml file=shared/ref.toml
[package]
name = "shared"
```

```ref file=shared/src/root.ref
\module Family(A: \Set) { \definition Carrier: \Set := A; }
```

```toml file=main/ref.toml
[package]
name = "main"
[dependencies]
shared = { path = "../shared" }
```

```ref file=main/src/root.ref
\module Local(A: \Set) { \definition Carrier: \Set := A; }
        \module Consumer {
            \definition dependency(A: \Set): \Set := shared.Family[A := A].Carrier;
            \definition rooted(A: \Set): \Set := \root.Local[A := A].Carrier;
            \definition same(A: \Set)(x: dependency A): rooted A := x;
        }
```

## packages resolve dependencies and local children

二つの依存経路で共有する package と局所的な子 module を同時に import できる。

```toml case
id = "packages_resolve_dependencies_and_local_children"
scope = "package"
expect = "accept"
entry = "app"
```

```toml file=shared/ref.toml
[package]
name = "shared"
```

```ref file=shared/src/root.ref
\module Truth { \definition proposition: \Prop := \forall (P: \Prop) -> P -> P; }
```

```toml file=left/ref.toml
[package]
name = "left"
[dependencies]
shared = { path = "../shared" }
```

```ref file=left/src/root.ref
\module Source { \import shared.Truth[] \as T; \definition proposition: \Prop := T.proposition; }
```

```toml file=right/ref.toml
[package]
name = "right"
[dependencies]
shared = { path = "../shared" }
```

```ref file=right/src/root.ref
\module Source { \import shared.Truth[] \as T; \definition proposition: \Prop := T.proposition; }
```

```toml file=app/ref.toml
[package]
name = "app"
[dependencies]
left = { path = "../left" }
right = { path = "../right" }
```

```ref file=app/src/root.ref
\module Client {
  \module Child { \definition proposition: \Prop := \forall (P: \Prop) -> P -> P; }
  \import .Child[] \as Local;
  \import left.Source[] \as L;
  \import right.Source[] \as R;
  \definition fromLeft: \Prop := L.proposition;
  \definition fromRight: \Prop := R.proposition;
  \definition fromChild: \Prop := Local.proposition;
}
```

## cyclic dependencies

package の依存が循環するため拒否される。

```toml case
id = "cyclic-dependencies"
scope = "package"
expect = "reject"
entry = "a"
```

```toml file=a/ref.toml
[package]
name = "a"
[dependencies]
b = { path = "../b" }
```

```toml file=b/ref.toml
[package]
name = "b"
[dependencies]
a = { path = "../a" }
```

```ref file=a/src/root.ref
\module Main {}
```

```ref file=b/src/root.ref
\module Main {}
```

## external parameter inference

外部 module の parameter に未解決の型が残るため拒否される。

```toml case
id = "external-parameter-inference"
scope = "package"
expect = "reject"
```

```ref file=src/root.ref
\module Child(A: _);
```

```ref file=src/Child.ref

```

## external program module parameters are instantiated in nested modules

Program の module parameter は外部ファイルの子 module にも代入される。

```toml case
id = "external_program_module_parameters_are_instantiated_in_nested_modules"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source(X: \VType, x: X);
\module Consumer {
  \inductive Unit: \VType := | unit: Unit;
  \import \root.Source[X := Unit, x := Unit::unit] \as S;
  \import \root.Source[X := Unit, x := Unit::unit].Child[] \as C;
  \check S.value: Unit;
  \check S.result: \F(Unit);
  \check C.value: Unit;
  \definition package: \Box[\F(Unit)] := \box[\F(Unit)](\return(C.value));
  \normalize \squash[\F(Unit)](package);
}
```

```ref file=src/Source.ref
\definition value: X := x;
\definition result: \F(X) := \return x;
\module Child;
```

```ref file=src/Source/Child.ref
\definition value: X := x;
```

## external child module inherits parent import aliases

外部ファイルにある子 module も親の import alias を利用できる。

```toml case
id = "external_child_module_inherits_parent_import_aliases"
scope = "package"
expect = "accept"
```

```ref file=src/root.ref
\module Source {
  \definition value: \Prop := \forall (P: \Prop) -> P -> P;
}
\module Parent;
```

```ref file=src/Parent.ref
\import \root.Source[] \as Shared;
\module Child;
```

```ref file=src/Parent/Child.ref
\definition inherited: \Prop := Shared.value;
```

## parent and external references share checked child declarations

親の内側からの参照と外側からの参照は同じ子 module の宣言を指す。
永続キャッシュを無効にしても、共有される宣言の検査は一回で済む。

```toml case
id = "parent_and_external_references_share_checked_child_declarations"
scope = "package"
expect = "accept"
args = ["--no-cache"]
env = { REF_TYPE_PROFILE_DECLARATIONS = "1" }
checks = [
  { stream = "stderr", pattern = 'definition marker \(excluding diagnostics\)', count = 1 },
]
```

```ref file=src/root.ref
\module Parent {
  \module Child { \definition marker: \Prop := \forall (P: \Prop) -> P -> P; }
  \import \root.Parent[].Child[] \as Local;
  \infer Local.marker;
}
\module Other {
  \import \root.Parent[].Child[] \as External;
  \infer External.marker;
}
```

