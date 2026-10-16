# cli / profiling

## 進捗の計測

進捗の計測を有効にした状態で、親と子の module を検査できる。

```toml scenario
id = "progress-and-timings"
scope = "module"
name = "Parent"
env = { REF_TYPE_PROFILE_PROGRESS = "1" }
```

```ref
\module Child { \infer \Set; }
```

### 初回

空のキャッシュで検査に成功する。

```toml step
id = "cold"
expect = "accept"
```

### 再利用

前回のキャッシュがある状態でも検査に成功する。

```toml step
id = "warm"
expect = "accept"
```

## 成功・失敗時の処理時間の内訳

処理時間の計測を有効にしても、正しい宣言は受理し、型が合わない宣言は拒否する。

```toml scenario
id = "cost-profiles"
scope = "module"
name = "Root"
args = ["--no-cache", "--no-progress", "--diagnostics", "compact"]
env = { REF_TYPE_PROFILE_COSTS = "resolve.total,kernel." }
```

```ref
\definition identity[P: \Prop][p: P]: P := p;
```

```toml step
id = "accepted"
expect = "accept"
```

```toml step
id = "rejected"
expect = "reject"
```

```ref
\definition invalid: \Prop := \Set;
```
