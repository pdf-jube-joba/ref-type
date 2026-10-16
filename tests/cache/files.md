# cache / files

## キャッシュ無効時の既存ファイルの保持

一度保存したキャッシュは、キャッシュ無効かつ容量上限ゼロで検査しても、ファイルの構成と内容が変わらない。

```toml scenario
id = "no-cache-preserves-files"
scope = "package"
cache_dir = "default"
```

```ref file=src/root.ref
\module M { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
```

### 保存

検査に成功するとキャッシュにファイルができる。

```toml step
id = "saved"
expect = "accept"
files = [{ path = "refcache", nonempty = true }]
```

### キャッシュ無効

検査に成功し、保存済みファイルは変わらない。

```toml step
id = "uncached"
expect = "accept"
args = ["--no-cache", "--cache-budget-mib", "0", "--no-progress"]
files = [{ path = "refcache", same_as = "saved", nonempty = true }]
```
