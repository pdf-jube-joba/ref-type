# 点に依存する商と点ごとの形式の型

`a8498cb` の処理系で、多様体・De Rham 計画の表現検査中に再現した G08 の比較プロジェクトである。
各 project は `std` の商構成を実際に読み込み、キャッシュなしで検査する。
現在の処理系では全5例が成功する。

`Space` は点の集合とベクトルの集合の宣言の束である。
`Representative[M, x]` は `x` に等しい点とベクトルを保持し、`Fiber[M, x]` はベクトルの等式による商を作る。
実際の接空間ではチャートと座標ベクトルを保持するが、ここでは点への依存と商の型の受け渡しだけに縮小している。
この例は接空間の数学的な構成を実装したものではない。

検査したい型は次である。

```text
\definition sections(M: Space)(k: N.Nat^): \Set :=
  \forall (x: M.Point) -> (Fin.Fin k -> fiber M x) -> M.Vector;
```

| project | 検査する構成 | 修正前 | 現在 |
| --- | --- | --- | --- |
| `01-direct-type` | 点ごとの型を直接書く | `sections` で `uncaptured parameter` | 成功 |
| `02-function-alias` | `Function(A, B): Set := A -> B` により二つの関数型を作る | 成功 | 成功 |
| `03-explicit-lambda` | 点ごとの `At.Form` を使い、lambda の引数を直接の関数型で注釈する | `copy` で `uncaptured parameter` | 成功 |
| `04-scoped-lambda` | 同じ `At.Form` を使い、引数型を `_` または `At.Arguments` で指定する | 両方の `copy` が成功 | 成功 |
| `05-alias-equality` | `02` の型に、点・有限引数列ごとの等式判定と外延性証明を追加する | `equal` で `expected Program value-type syntax` | 成功 |

`01` と `03` の診断は `ModuleParamId` の module と position を含む。
module の数値 ID は読み込む宣言の構成で変わるので、比較対象は `uncaptured parameter` と失敗する定義の位置である。
修正前の `05` は、先行する `equal` が失敗したため外延性証明へ到達しなかった。

修正前の `02` と `04` は、型値の定義と点ごとの module による回避例である。
局所具体化の束縛変数の型に現れる module parameter も capture の依存に含める修正により、すべての表現が成功する。
[利用側の外延性検査](../../../tests/projects/manifolds-de-rham/src/Pointwise.ref)と[次数で台集合が変わるコホモロジーの利用例](../../../tests/projects/manifolds-de-rham/src/Cohomology.ref)も検査に成功する。

## 実行

リポジトリのルートから実行する。

```sh
cargo build -p cli --locked
python3 _plans/reproductions/g08-pointwise-quotient/check.py
```

スクリプトは各 project の終了コードと診断を確認する。
終了コード 0 は、成功例と既知の失敗例がこの表どおりに再現したことを意味する。
失敗例を修正した処理系ではスクリプトも更新する。
個別に検査する場合は、次のように project を指定する。

```sh
target/debug/cli _plans/reproductions/g08-pointwise-quotient/01-direct-type --no-cache --diagnostics compact
target/debug/cli _plans/reproductions/g08-pointwise-quotient/04-scoped-lambda --no-cache --diagnostics compact
```

## 計画への影響

[多様体・De Rham 計画](../../manifolds-de-rham.md)の第4節の点に依存する接空間、第6節の点ごとの交代形式の解釈と等式判定に関係する。
計画末尾の、処理系の障害を再現例・診断・影響範囲とともに記録して停止する条件に従い、今回の実装を停止した。
第1〜8節の数学的実装と最終利用例は未完了である。
再開時には、成功例の表現を実際の交代形式・引き戻し・外積の API へ拡張して検査するか、処理系を修正して直接の表現を検査する。
