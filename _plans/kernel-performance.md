# kernel のコピー・キャッシュ・評価走査を改善する

## 対象

`src/kernel` の型検査・変換可能性判定・正規化・Program 評価を計測し、寄与の大きい処理から改善する。性能改善率は計測して判断する。

| 箇所 | 現在の処理 | 調べるコスト |
| --- | --- | --- |
| `Arena::get` / `read`、`structure::map_children` | 型付きノードを intern し、arena と interner は `Rc` で共有する。`get` と変換時にはノードを clone する | 可変長フィールドのコピー、変更のない変換での確保 |
| `Checker::infer` / `check_context` | context の classifier 列を `Vec` に集め、キャッシュの検索や検証済み context との照合に使う | 深い context の確保・走査・ハッシュ |
| `convertible` / `alpha_equal` | 再帰的な α 同値比較の後に、比較中のペアキャッシュを参照する。α 同値比較自体にはメモ化がない | 共有部分の重複比較 |
| `evaluate` / `reduce_once` | 一段簡約ごとに根から評価位置を探索し、祖先ノードを再構築する | 深い評価位置への再走査・再構築 |

参照: [syntax.rs](../src/kernel/src/syntax.rs)、[check.rs](../src/kernel/src/check.rs)、[calculus.rs](../src/kernel/src/calculus.rs)、[traversal.rs](../src/kernel/src/structure/traversal.rs)、[comparison.rs](../src/kernel/src/structure/comparison.rs)、[environment.rs](../src/kernel/src/environment.rs)。

## 1. kernel を直接測る基準を作る

[既存ハーネス](../src/cli/benches/performance.rs) に `kernel/` 接頭辞のケースを追加する。現在の `normalize/beta256` と `evaluate/countdown*` は `front::raw` を呼ぶため、kernel 単体の測定ケースを用意する。

| ケース群 | 入力と計測対象 |
| --- | --- |
| `kernel/infer/*` | 浅い／深い context、共有部分の多い型の推論・検査 |
| `kernel/convertible/*` | 同一 handle、別 handle で α 同値、β 簡約後に同値、深い位置で不一致になる式 |
| `kernel/substitute/*` | 開いた／閉じた引数、異なる束縛の深さと部分式の共有率 |
| `kernel/normalize/*` | β 簡約の列と、深い位置に簡約可能な式がある入力 |
| `kernel/evaluate/*` | カウントダウン、深い Sequence・関数適用、certificate を持つ Box |

- 入力サイズを複数用意し、増加傾向を見る。
- 構文・環境の準備、lowering、結果検証を計測外に置く。
- 各反復に新しい環境を使う。キャッシュが空のケースと、反復内で事前呼び出しを行う再利用ケースを分ける。準備や検証によるキャッシュの更新も管理する。
- 時間の中央値とばらつきを測る。割り当て量、arena ノード数、キャッシュの保持量、訪問数は別の診断実行で調べる。
- `check/library` と `pipeline/library` で実利用全体への影響も確認する。

ケース追加後は[計測手順](../src/cli/benches/README.md)に従い、同じ入力・ビルド条件で基準を保存して比較する。

## 2. 残るノードコピーを減らす

`get` による読み取りと、`map_children` が変換前に行う clone を計測する。特に帰納型の引数・分岐を持つノードと、結果が変わらず元 handle を返す変換を調べる。

- 読み取り専用の処理では `read` の共有参照を使い、必要なフィールドだけを取得する。
- 変更のない変換でコピーが支配的なら、子の変更を確認してからノードを構築する方式を比較する。
- `shift` / `substitute` のメモ化と `max_loose_bound` による走査省略を維持する。
- 共有元の不変性、構造による interning、束縛の深さと証明注釈の変換を保つ。

採用条件は、対象ケースのコピー・確保量が減り、共有ノードや深い構文でも型・簡約結果を維持すること。

## 3. 型推論のキャッシュキーを ContextId にする

classifier 列を空 context と `(親ContextId, classifier)` で共有し、推論キーを `(Expression, ContextId)` にする。共有表は `Environment` に保持し、別の `Checker` でも同じ列には同じ ID を使う。

- `under` の push/pop と、エラー時の復元に ID の更新を合わせる。
- 公開されている `Checker::context` の変更は公開の推論入口で照合し、内部再帰は差分更新する。
- `check_context` が prefix ごとに検査する間も ID を同期し、不正な context でキャッシュを利用しない。
- binder 名をキーから除く規則を保ち、classifier の順序・family・level を区別する。ハッシュ衝突時も列の同一性を確認する。
- 宣言登録時の推論・WHNF キャッシュ無効化と共有表の寿命を整合させる。

深い context でキー生成の確保・走査が減ることに加え、浅い context の管理費と共有表の保持量を確認する。

## 4. 変換可能性判定の重複走査を減らす

同一 handle と family・sort を判定した後、既存のペアキャッシュを `alpha_equal` より先に参照する。共有部分の比較が残る主要コストなら、α 同値比較にも一回の比較全体で共有するメモ化を導入する。

- binder 名を無視する規則、family・level、証明注釈の erasure を維持する。
- 完了した比較結果だけを保存し、エラーを不一致としてキャッシュしない。
- 共有の多い式と小さな式の両方で、訪問数とメモ化の管理費を比較する。

α 同値・β 同値・不一致の結果を維持し、同じ部分式ペアの再走査を減らす。

## 5. 評価位置を保持する

再走査・祖先再構築が主要コストなら、評価位置と周囲の構文をフレームのスタックに保持する内部評価ループを実装する。

- 現行 `reduce_once` を比較基準にし、Program の評価位置、ValueTerm が step しない規則、各 family の走査順を維持する。
- fuel を一段簡約に対応させる。`fuel = 0`、正規形に到達する境界、`OutOfFuel` の途中結果も比較する。評価位置の移動だけでは fuel を消費しない。
- Box の簡約と `advance_certificate` の更新タイミングを保存する。
- β 簡約には既存の `substitute` を使う。

深い入力で再走査・再構築が減り、各 fuel 境界の式と certificate の対応を維持できることを採用条件にする。

## 検証と記録

各実装段階で `cargo clippy -p kernel --all-targets -- -D warnings` と `cargo test --workspace` を実行する。回帰テストは、共有ノード、context の変更・エラー後の復元、環境更新、証明注釈、評価途中の状態など変更が影響する境界に絞る。

対象ケースと実利用ケースの時間・ばらつき・割り当て量・保持量を記録する。測定のばらつきを超える効果を確認し、次の作業は残った主要コストから選ぶ。
