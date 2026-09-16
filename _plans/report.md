# 実数ライブラリの型検査遅延の切り分け（2026-09-16）

## 結論

主因は DedekindReal.Order.linearOrder のカーネル検査で行われる不要な完全正規化。
元の簡約処理を保った計測ビルドを長時間実行したところ、約13分後に
`normalization fuel exhausted` で終了した。1200秒の外部タイムアウトには達していない。
デッドロックではなく、CPUを使って正規化を続け、内部の100000ステップ上限で失敗する。

さらに独立したフロント側の性能問題と、refinement関数の簡約不足がある。
診断用コピーでこの3点に対応する実験的な分岐を有効化すると、数学側を変更せずに
`lib/root.ref` と `lib/tests.ref` がそれぞれ約16秒でカーネル検査まで完了した。
これは現在記述されているライブラリの型検査結果であり、未記述の完備順序体の証明が完成したという意味ではない。

作業ツリーの処理系・ライブラリには、この調査による変更を適用していない。
このディレクトリにある `src/` と `lib/` は調査開始時のコピーで、計測・実験変更はコピーのみに入っている。

## 1. カーネル：帰納型簡約でコンストラクタ型を完全正規化

対象：元の `src/kernel/src/calculus.rs:411`、`reduce_inductive` 内の
`ty = normalize(env, ty)?`。

コンストラクタ引数を取り出すためには型の先頭の積を露出すればよいが、
実際には型全体を正規化している。レコードや対の射影でも、型パラメータに入った
大きなrefinementの内部まで展開される。`normalize` は `reduce_once` を繰り返し、
`reduce_once` は木を巡回するため、共有された部分式があっても大量の再走査になる。
同じファイルの `recursive_case_argument`（元の347行目）にも完全正規化があるが、
今回の原因確認実験ではそちらは変更していない。

`lib/DedekindReal/Order.ref:60` の `linearOrder` は、フロント側の型検査を通り、
カーネル向け本体変換も約0.002〜0.007秒で終わる。その後のカーネル再検査で遅延する。

観測：

- `kernel-profile.log`：全体の経過時間12分52.95秒、CPU時間767.35秒、終了コード1。
- エラー：`indexed definition DefId { module: ModuleId(246), index: 7 }: normalization fuel exhausted`。
- `head-experiment.log`：411行目だけを `whnf` に切り替えた試験で、同じ定義のカーネル検査が0.012147秒。
- この試験ではDedekind全体のカーネル段階も0.210549秒で完了し、その先のCauchy側に進む。

### 実数非依存の再現例

`minimal.ref` / `minimal12.ref` / `minimal14.ref`。
`T0 = Unit`, `T(n+1) = Pair[Tn,Tn]` と置き、
`first Tn Tn (pair x x) = x` を `refl(x)` で証明するだけ。

| 型の深さ | 元の簡約処理による定義単位の検査時間（debug） |
| --- | ---: |
| 4 | 0.0058秒 |
| 6 | 0.079秒 |
| 8 | 1.086秒 |
| 10 | 15.18秒 |
| 12 | 264.53秒（正常完了） |

深さ14はreleaseビルドでも約5分後に正規化上限で失敗した。
`minimal14-release.log` の最後の定期集計では `reduce_once` 呼び出しが約47.6億回。
同じファイルを先頭簡約の実験分岐で検査すると1ミリ秒未満のカーネル段階で通る。
debugだけの問題でも、実数の数学的内容による難しさでもない。

## 2. フロント：共通する関数の本体を先に展開してしまう

対象：元の `src/front/src/raw/calculus.rs:637` 以降の `alpha_rec`。

最初の短絡判定は簡約なしの構文一致のみ。例えば `P (identity x)` と `P x` の比較で
これに失敗すると、引数の等価性を調べる前に両側の `P` の実装を展開する。
Cauchyの `Close` などでは有理数・整数・自然数の実装まで展開され、巨大な一時式を作る。

`no-bridge.log`（Dedekindの接続証明だけを外したコピー）でのフロント側所要時間：

- `equivalentRefl` の本体elaboration：約14.23秒。
- `pointwiseEquivalent` の本体elaboration：約14.46秒。
- `constCauchyOf` の検査：約13.83秒。
- `negCauchy` の本体elaboration：約39.78秒。
- プロセス全体の最大RSS：約4.06GiB。

`raw-conversion.log` では時間が `erased_convertible` の単独呼び出しに集中していることも確認。
共通headの適用を先に合同則で比較する実験では、上記の各段階は概ね0.0005〜0.0015秒になった。
この実験だけでは次項の問題は解消しない。実際、失敗する比較で長くなる経路も残るため、
本体への採用時は失敗経路・キャッシュ・探索順序も検証する必要がある。

### 実数非依存の再現例

`common-head20.ref`：`P0 x := x=x`, `P(n+1) x := Both[Pn x,Pn x]` とし、
`h : Pn (identity x)` から `Pn x` を単に `h` で証明する。

| n | フロントの定義処理時間（元の比較処理、debug） |
| --- | ---: |
| 14 | 0.42秒 |
| 16 | 1.81秒 |
| 18 | 6.99秒 |
| 20 | 30.36秒 |

ファイル全体は約37秒・787MiB。共通head比較の実験では約0.01秒・11MiBで通る。
カーネル段階は両方とも約0.01秒で、1とは独立したフロント側の問題である。

## 3. フロント：refinementに包まれた関数の適用が簡約されない

対象：元の `src/front/src/raw/calculus.rs:703` 以降のApp簡約。
関数位置を `whnf` にしても `SubsetIntro` に対する場合分けがなく、その内部のlambdaまで進めない。
式の外側でのrefinement消去はあっても、関数適用の内側では進まない。

独立した8行の再現例：`refined-function.ref`。
恒等関数を `Ty(Unit -> Unit, Functions)` に包み、`identity x = x` を `refl(x)` で証明すると
フロントの `ty, inferred_ty not convertible` で失敗する。

実際の停止箇所は `lib/CauchyReal/Sequences.ref:65` の `negRespects`。
`at (neg x) n` と `negRat (at x n)` の対応に、この簡約が必要。
フロントのAppにrefinementの中へ進む実験分岐を入れると、独立例もライブラリも既存のカーネル再検査を通る。
これは数学的に不正な証明を発見したというより、フロントとカーネルの簡約の不一致である。

## 総合実験・検証範囲

3つの実験分岐を有効にして：

- `lib/root.ref`：exit 0、約16.18秒、RSS 301932KiB。
- `lib/tests.ref`：exit 0、約16.45秒、RSS 323492KiB。
- `cargo test --workspace --lib`：front 131件、kernel 28件、すべて成功。

カーネル検査を省略した結果ではない。ただし実験分岐は本番用の修正として整備したものではなく、
全integration test・境界事例・失敗経路についての回帰検証は未完了。
診断ビルド・計測負荷・一部試験の並行実行を含むため、時刻は厳密なベンチマーク値ではなく目安。
log内の定義単位タイマーと `/usr/bin/time` の総時間には差があるため、表ではどちらかを明示した。

## 再実行

このディレクトリで：

```sh
cargo build --offline -p cli
# 元の処理：非常に長い。外部上限1200秒より先に内部正規化上限で失敗した。
REF_PROFILE=1 REF_KERNEL_PROFILE=1 target/debug/cli lib/root.ref

# 3点の切り分け用分岐を有効化（コピー内のみ）
REF_PROFILE=1 REF_EXPERIMENT_WHNF=1 REF_EXPERIMENT_CONGRUENCE=1 REF_EXPERIMENT_REFINEMENT=1 target/debug/cli lib/root.ref

# 独立例
REF_PROFILE=1 target/debug/cli minimal12.ref
REF_PROFILE=1 REF_EXPERIMENT_WHNF=1 target/debug/cli minimal12.ref
REF_PROFILE=1 target/debug/cli common-head20.ref
REF_PROFILE=1 REF_EXPERIMENT_CONGRUENCE=1 target/debug/cli common-head20.ref
target/debug/cli refined-function.ref
REF_EXPERIMENT_REFINEMENT=1 target/debug/cli refined-function.ref
```

数学ライブラリを更に書き換える前に、1、3、2の順で小さな回帰試験を付けて処理系側を修正するのが次の候補。
1と2は簡約順序・計算量の問題であり、タイムアウトの延長や正規化fuelの増加だけでは解決しない。