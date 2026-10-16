# cli / terminal

## パッケージごとの完了表示

依存元と依存先のそれぞれについて、検査・スキップの件数を制御端末へ一回ずつ表示する。
各パッケージの完了表示は全体の完了表示より先に出る。

```toml scenario
id = "package-summaries"
scope = "workspace"
entry = "app"
terminal = true
args = ["--progress-tty"]
```

```toml file=app/ref.toml
[package]
name = "app"
[dependencies]
base = { path = "../base" }
```

```ref file=app/src/root.ref
\module Main { \import base.A[] \as A; \definition P: \Prop := A.P; }
```

```toml file=base/ref.toml
[package]
name = "base"
```

```ref file=base/src/root.ref
\module A { \definition P: \Prop := \forall (P: \Prop) -> P -> P; }
```

### 初回

両パッケージの二つの module を検査する。

```toml step
id = "cold"
expect = "accept"
checks = [
  { stream = "terminal", pattern = 'Finished app: 2 check, 0 skip', count = 1 },
  { stream = "terminal", pattern = 'Finished base: 2 check, 0 skip', count = 1 },
  { stream = "terminal", ordered = ["Finished app: 2 check, 0 skip", "Finished 4/4 modules"] },
  { stream = "terminal", ordered = ["Finished base: 2 check, 0 skip", "Finished 4/4 modules"] },
  { stream = "stderr", absent = ["Finished app:", "Finished base:"] },
]
```

### 再利用

両パッケージの二つの module をスキップする。

```toml step
id = "warm"
expect = "accept"
checks = [
  { stream = "terminal", pattern = 'Finished app: 0 check, 2 skip', count = 1 },
  { stream = "terminal", pattern = 'Finished base: 0 check, 2 skip', count = 1 },
  { stream = "terminal", ordered = ["Finished app: 0 check, 2 skip", "Finished 4/4 modules"] },
  { stream = "terminal", ordered = ["Finished base: 0 check, 2 skip", "Finished 4/4 modules"] },
  { stream = "stderr", absent = ["Finished app:", "Finished base:"] },
]
```

### 進捗表示の無効化

進捗表示と計測を無効にすると、端末と標準エラーへの出力がなくなる。

```toml step
id = "quiet"
expect = "accept"
terminal = false
args = ["--no-progress"]
stderr_empty = true
```

## 端末と詳細ログの出力先

標準出力と標準エラーをファイルに保存しても、進捗バーと完了表示は制御端末に出る。
宣言・進捗の計測と所要時間は標準エラーに残る。

```toml case
id = "terminal-and-log"
scope = "module"
name = "Test"
parameters = 'A: \Set'
expect = "accept"
terminal = true
args = ["--no-cache", "--progress-tty"]
env = { REF_TYPE_PROFILE_PROGRESS = "1", REF_TYPE_PROFILE_DECLARATIONS = "1" }
checks = [
  { stream = "terminal", contains = ["\u001b[2K", "Finished"], absent = ["checking ", "progress elapsed_seconds="] },
  { stream = "stderr", contains = ["checking ", "event=finished success=true", "\ncheck ", "\ntotal ("], absent = ["\u001b[2K"] },
]
```

```ref
\definition B: \Set := A;
```

## Ctrl+C による中断

進捗バーと宣言の処理開始が観測できた時点で制御端末へ Ctrl+C を送り、SIGINT で終了することを確認する。
開始までの計測ログは保存され、完了イベントは出力されない。

```toml case
id = "ctrl-c"
scope = "module"
name = "Slow"
expect = "interrupted"
terminal = true
timeout = 15
args = ["--no-cache", "--progress-tty"]
env = { REF_TYPE_PROFILE_PROGRESS = "1", REF_TYPE_PROFILE_DECLARATIONS = "1" }
interrupt = { terminal = "\u001b[2K", stderr = "checking " }
checks = [
  { stream = "terminal", contains = ["\u001b[2K"] },
  { stream = "stderr", contains = ["event=start module=", "checking "], absent = ["event=finished success=true", "\u001b[2K"] },
]
```

```ref repeat=2000
\check (\forall (P: \Prop) -> P -> P): \Prop;
```
