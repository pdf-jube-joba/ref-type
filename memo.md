## 2025/07/22
typst が壊れていた。
```
error: type state has no method `display`
    ┌─ @preview/ctheorems:1.1.2/lib.typ:167:15
    │
167 │   thm-qed-done.display()
    │                ^^^^^^^

help: error occurred while importing this module
  ┌─ main.typ:1:8
  │
1 │ #import "@preview/ctheorems:1.1.2": *
  │   
```
ctheorem をバージョンアップしたら大丈夫になった。

ただ、個々のページとして見つつ、ほかのところへも移りたいことが多いので、
pdf をわけるよりもwebページっぽい方がいい。

変更前にいったん、エラーがなくなった状態でコミットする。
