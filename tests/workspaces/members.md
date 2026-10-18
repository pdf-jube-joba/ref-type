# workspaces / members

## workspace の member

manifest に列挙した member を検査する。
列挙していない package は対象に含めない。

```toml scenario
id = "members"
scope = "workspace"
```

```toml file=ref.toml
[workspace]
packages = ['left', 'right', 'left/../left']
```

```toml file=left/ref.toml
[package]
name = 'left'
```

```ref file=left/src/root.ref
\module Main {}
```

```toml file=right/ref.toml
[package]
name = 'right'
```

```ref file=right/src/root.ref
\module Main {}
```

```toml file=unlisted/ref.toml
[package]
name = 'unlisted'
```

```ref file=unlisted/src/root.ref
\module Broken { \definition bad: \Prop := \Set; }
```

### 列挙した member

列挙した member のソースは正しい。

```toml step
id = "valid"
expect = "accept"
```

### member の型エラー

列挙した member の型エラーは拒否される。

```toml step
id = "broken"
expect = "reject"
```

```ref file=right/src/root.ref
\module Main { \definition bad: \Prop := \Set; }
```

### member の欠落

manifest に列挙した package のファイルがない。

```toml step
id = "missing-file"
expect = "reject"
remove = ["right/ref.toml"]
```

## ルート自身も package である workspace

ルートの package と子の member を同じ workspace として検査できる。

```toml case
id = "root-package"
scope = "workspace"
expect = "accept"
```

```toml file=ref.toml
[package]
name = 'app'
[workspace]
packages = ['member', '.']
[dependencies]
member = {path = 'member'}
```

```ref file=src/root.ref
\module Main { \import member.Core[] \as M; \definition P: \Prop := M.P; }
```

```toml file=member/ref.toml
[package]
name = 'member'
```

```ref file=member/src/root.ref
\module Core { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
```

