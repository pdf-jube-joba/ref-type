# workspaces / members

## Workspace members

Check the members listed in the manifest.
Packages not listed are excluded from the scope.

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

### Listed members

The listed members' sources are valid.

```toml step
id = "valid"
expect = "accept"
```

### Member type error

A type error in a listed member is rejected.

```toml step
id = "broken"
expect = "reject"
```

```ref file=right/src/root.ref
\module Main { \definition bad: \Prop := \Set; }
```

### Missing member

Files for a package listed in the manifest are missing.

```toml step
id = "missing-file"
expect = "reject"
remove = ["right/ref.toml"]
```

## Workspace whose root is also a package

The root package and child members can be checked as one workspace.

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

