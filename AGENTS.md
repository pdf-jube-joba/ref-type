## .md へ書き込むとき
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

## 計測や分析
perf は `/usr/lib/linux-tools/6.8.0-139-generic/perf` にあります。

## コードの書き方の方針
- 古い構文を reject することをチェックするためだけのテストは書かない。
- コードをきれいに保つ。既存の rust コードを大きく変更してかまわない。簡潔さや規則性を既存のコードよりも尊重する。
- コードのデバッグ用に kernel に作って便利だった機能は残す。

### 過去の微妙だった点
- `()` をつけなくていいところにつける `(x)` とか。
- 一気に生成しすぎているのか、こういうミスをやってる？
  ```
  • Edited lib/Reals/CauchyReal/Sequences.ref (+2 -2)
  1082     \forall (j: Nat) -> NatLe k j ->
  1083 -     RationalOperations.Le s (at y j)] }, N))}
  1083 + RationalOperations.Le s (at y j)] }, N))}
  1084   n (NL.leTrans N (commonBound M N) n
  1085 -   (rightLeCommonBound M N) Kn)) },
  1085 +   (rightLeCommonBound M N) Kn))) },
  1086   \Cast[Nat] ({ k : Nat \where
  ```
  括弧の対応をちゃんとみればよさそうだが、その前に大量の定義を入れるのをやめたい。 `--parse-only` を使う。
- こういう定義は `byCases` がそのままゴールなので無駄っぽい。
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
- できれば `_` を型の位置には使うようにしてほしい。
  ```
  \definition diffStepSet: DiffState^ -> \RunStep[DiffState^, Int^] := \squash[\F(\U((DiffState -> \RunStep[DiffState, Int])))](\box[\F(\U((DiffState -> \RunStep[DiffState, Int])))](\return diffStep));
  ```
  こういうのをやめる。
- `\cfun ... \return \thunk` を `\fun` に移行しようという命令に対して、機械的に移行しようとしたところ括弧の数が変わって対応が取れなくなった。
  ```
  • 括弧と内部の式を壊さずに戻せました。次に add だけで、外側の \cfun を \fun に置換
  し、\return(\thunk(...)) はそのまま残す形を試します。これが通れば同じ規則を全対象へ適用します。
  ```
  もとの要件を満たせないみたいな感じにいって途中までやるのをやめるべき。機械的な移行（ python や perl ）に失敗したなら、 ちゃんと理由を分析して python や perl を書き直すようにして、元の内容を変更しない。
- `mulIntegerDistribLeft` とかすごい長い。
- `mulIntegerDistribLeft` はブロック使ったら何とかなりそう。
- `addMonotone` もどんどんインデントをしていく。インデントをすること自体は自然な内容だが、もっと分割できないか。
