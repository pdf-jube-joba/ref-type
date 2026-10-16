# cli / profiling

## 進捗イベントと所要時間

親と子の開始・完了イベントを出力し、全体の完了後に各 module の所要時間を出力する。
module と共有処理の時間の合計は、丸め誤差の範囲で全体の所要時間に一致する。

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

親と子の検査を開始してから完了する。
パイプに出力するログには端末用の復帰文字を含めない。

```toml step
id = "cold"
expect = "accept"
checks = [
  { stream = "stderr", contains = ["event=planned", "event=finished success=true"], absent = ["\r"] },
  { stream = "stderr", ordered = ["event=start module=Parent package_completed=", "event=complete action=Check module=Parent module_seconds="] },
  { stream = "stderr", ordered = ["event=start module=Parent.Child package_completed=", "event=complete action=Check module=Parent.Child module_seconds="] },
  { stream = "stderr", ordered = ["event=finished", "check Parent ("] },
  { stream = "stderr", pattern = '^check Parent \([\d.]+s\)$', count = 1 },
  { stream = "stderr", pattern = '^check Parent\.Child \([\d.]+s\)$', count = 1 },
  { stream = "stderr", pattern = '^(?:check Parent(?:\.Child)?|shared) \(([\d.]+)s\)$', count = 3, sum_equals = '^total \(([\d.]+)s\)$', relative_tolerance = 0.01, positive = true },
]
```

### 再利用

検査済みの module はスキップとして記録する。

```toml step
id = "warm"
expect = "accept"
checks = [
  { stream = "stderr", contains = ["event=planned", "event=finished success=true", "event=complete action=Skip module=Parent module_seconds=", "event=complete action=Skip module=Parent.Child module_seconds="], absent = ["\r"] },
  { stream = "stderr", ordered = ["event=finished", "skip Parent ("] },
  { stream = "stderr", pattern = '^skip Parent \([\d.]+s\)$', count = 1 },
  { stream = "stderr", pattern = '^skip Parent\.Child \([\d.]+s\)$', count = 1 },
  { stream = "stderr", pattern = '^(?:skip Parent(?:\.Child)?|shared) \(([\d.]+)s\)$', count = 3, sum_equals = '^total \(([\d.]+)s\)$', relative_tolerance = 0.01, positive = true },
]
```

## 成功・失敗時の処理時間の内訳

受理・拒否のどちらでも、指定した処理と kernel の集計を標準エラーに出力する。
処理全体の集計は一回で、選択範囲外の処理は個別に出力しない。

```toml scenario
id = "cost-profiles"
scope = "module"
name = "Root"
args = ["--no-cache", "--no-progress", "--diagnostics", "compact"]
env = { REF_TYPE_PROFILE_COSTS = "resolve.total,kernel." }
checks = [
  { stream = "stderr", contains = ["cost=resolve.total calls=1", "cost_group=kernel exclusive_us="], absent = ["cost=resolve.front-binding"] },
  { stream = "stderr", pattern = 'cost_total elapsed_us=', count = 1 },
  { stream = "stdout", absent = ["cost="] },
]
```

```ref
\definition identity(P: \Prop)(p: P): P := p;
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
