# Package の仕様
rust っぽい方向かつ `.lock` はなしの方向にする。

```ref.toml
[package]
name = "real"

[dependencies]
std = { path = "../std" }
```

- `./ref.toml` にパッケージ情報、 `./src/` にコード、 `./src/root.ref` がコードのエントリポイントとする。
- version 周りは入れないが、将来的に入れることを見越して内部的には Name ではなくて Id を見るようにする。
- 参照先は path のみとする。 `git = { ... }` とかの方向はなし。 `path = { ... }` のみ。
- 他のパッケージをコード中で参照するときは、 `otherPackageName.moduleName[]` とする。
  - 現状の子 module を import するときの `Child[].Descendant[]` という書き方はやめて、一番初めに `.` をつける。

```
\import .Child[].Descendant[] \as Loc; // これは自分の子モジュール
\import Other.Descendant[] \as Loc; // これは他のパッケージ `Other` の module の参照。
```

## 現在のコードを package 化する。
- `libs/` という名前にする。
- `libs/std/`, `libs/real/`, `libs/topology/` にわけてそれぞれパッケージにする。