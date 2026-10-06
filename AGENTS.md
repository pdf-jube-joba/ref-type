`> [!note]` で始まってるのは人間のメモです。書き換えないでください。

## 計測や分析
ローカル環境の場合には perf は `/usr/lib/linux-tools/7.0.0-38-generic` にあります。
クラウドで AI が動いている場合は perf、hyperfine、GNU time、valgrind、heaptrack がそのまま使えます。

## 実装のやりかた
重要な点: `_plans/` に書かれている1つのプランの実装時は、最後までやってから停止する。
途中のステップで停止しないこと。
そのプランの実装上発生した問題については、すべての決定権を託します。
実装ができないことがわかったらタスクを停止してください。

## 全体的なコードの書き方の方針
- 古い構文を reject することをチェックするためだけのテストは書かない。
- コードをきれいに保つ。既存のコードを大きく変更してかまわない。簡潔さや規則性を既存のコードよりも尊重する。

> [!warning]
> これは個人プロジェクトで、構文どころか基礎理論さえも変更します。（結構頻繁に）。
> 既存コードの尊重をしても意味ないです。
> 読みやすくて一貫性があれば、どれだけ変更しても構わないです。

## markdown
- 数式を書くときは `\(\)` と `\[\]` を使う
- チャットに由来する「○○しないこと」の判断は、 .md に残さない。
- 改行を入れるのは句読点を入れて不自然じゃないときにする。
  ```
  記号列は可能な限り一つのトークンになる。隣接する二つの記号トークンを意図する場合は空白で
  区切る。次の記号には構文上の意味がある。
  ```
  こういうのは気持ち悪い。次の行に `区切る。`だけ入れてるが、前の行に入れた方が見やすい。
  基本的に1行1文にして、 `、` を入れて不自然じゃないとき、かつ、次の行に2文以上入らないときのみ行を分ける。
- 具体例で推測できることは書かない。
  例: module のインスタンスの例で `\import \root.Top[A := T] \as T0;` と書いた場合、
  「 `[]` が要る。」は具体例から推測できるのでいらないし、 `Name[name := expression, ...]` と書くことも推測できるのでいらない。
- 例はあくまでも例なので、例示されたものだけを直すのではなくて他のものも直す。

## rust
- コードのデバッグ用に kernel に作って便利だった機能は残す。

## ref-type(このリポジトリの言語)
思ってた書き方ができなかった場合、「こう書きたい」の要望を `gaps.md` に書く。

### 基本方針
- `\definition` を使えるところは使い、できないときだけ `\alias` を使う。
- `\structure`, `\machine`, `\correspondence` を使う。
  - `Logic.And[P, Logic.And[Q, ]` みたいに入れ子が現れたら record を使えないか考える。言語の制約上 record を使えないことがわかった場合は使ってよい。
- あまりに重複する別 module の参照は definition で名前を付ける。
- ちゃんとライブラリを分ける。
- "定理"と呼ばれるものは仮定なしで示す。 定義の引数や module parameter で仮定を渡さない。

### 細かい方針

#### `()` でくくらなくていいならくくらない。

#### 複雑な式を避ける

例: こういう定義は `byCases` がそのままゴールなので無駄っぽい。
  ```
  \definition eqOfEqbTrue: \forall (a, b: Bool^) -> IsTrue (eqbSet a b) -> a = b :=
  \block {
    \fix (a, b: Bool^);
    \fix (e: IsTrue (eqbSet a b));
    \let byCases: \forall (a, b: Bool^) -> IsTrue (eqbSet a b) -> a = b :=
      \induction (a: Bool^) \return \forall (b: Bool^) -> IsTrue (eqbSet a b) -> a = b \with {
        | false => (\induction (b: Bool^) \return IsTrue (eqbSet Bool^::false b) -> Bool^::false = b \with {
          | false => (\fun (e: Bool^::true = Bool^::true) => \refl(Bool^::false))
          | true => (\fun (e: Bool^::false = Bool^::true) => absurd (Bool^::false = Bool^::true) e)
          })
        | true => (\induction (b: Bool^) \return IsTrue (eqbSet Bool^::true b) -> Bool^::true = b \with {
          | false => (\fun (e: Bool^::false = Bool^::true) => absurd (Bool^::true = Bool^::false) e)
          | true => (\fun (e: Bool^::true = Bool^::true) => \refl(Bool^::true))
          })
        };
    \return byCases a b e;
  };
  ```

#### インデントが深くなるものはブロック構文を使う

#### `_` を型の位置に使う

#### 数学的に自然な引数をとるようにする

例: 積位相の定義は、各 "位相" に対して行われるので、これは不自然。
```Product.ref
\definition topology(left: \Pow (\Pow A)) (right: \Pow (\Pow B)):
  ProductTopology :=
  ProductSpace.generated (Basis left right);
```
とるべき引数は `Topology::[Set]`

#### タスクは最後までやってから停止する
以下の場合を除き最後までやる。
- 体系の制限により書くことができない場合
- 言語処理系の制限により書くことができない場合

`まだ未証明です。` と書くことになった場合は上記のいずれかの理由を書く。
それ以外の場合は続ける。
ごまかしたり途中まで停止して報告しない。
最後までやる。
