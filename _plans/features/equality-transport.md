# 等式による集合値の移送の実装プラン

## 到達点

[G12](../gaps.md#g12) の集合値の移送を、等式の成立を前提とする原始項として追加する。
既存の `\idelim` で集合値の族を指定でき、自己移送の恒等性は命題上の等式として証明できるようにする。
恒等則から合成則と自然性をライブラリで証明し、微分形式の `Regrade.cast` をこの移送へ置き換える。
体系の記述、kernel、表面構文、標準ライブラリ、微分形式の利用側、キャッシュと検証までを一つの実装単位とする。

## 体系の規則

[system.md](../../doc/book/src/system.md) の原始構文に、族の body を束縛する次の項を追加する。

\[
\operatorname{transport}_{A}(a,b,x.B,u).
\]

\(x\) の束縛範囲は \(B\) とする。
\(A\)、\(a\)、\(b\)、\(u\) は外側の文脈で解釈する。
\(B_a:=B[x:=a]\)、\(B_b:=B[x:=b]\) と略記し、次の型判断を追加する。

\[
\frac{
  \Gamma\vdash A:*^s_i
  \qquad \Gamma\vdash a:A
  \qquad \Gamma\vdash b:A
  \qquad \Gamma,x:A\vdash B:*^s_j
  \qquad \Gamma\vdash u:B_a
  \qquad \Gamma\vDash a=b
}{
  \Gamma\vdash\operatorname{transport}_{A}(a,b,x.B,u):B_b
}.
\]

\(i\) と \(j\) は独立した集合の level とする。
恒等則は、同じ形成条件と \(\Gamma\vdash u:B_a\) の下で次の provability 規則として追加する。

\[
\Gamma\vDash\operatorname{transport}_{A}(a,a,x.B,u)=u.
\]

自己移送の型付けに必要な \(a=a\) は既存の `id intro` から得る。
`system.md` の transport は等式の導出を前提に持ち、その証明を項の引数に含めない。
既存の命題値の `id elim` と集合値の transport は、それぞれ provability と typing の規則として記載する。
恒等則の左辺と右辺は共通の集合 \(B_a\) の元として等式を形成する。

transport の head は neutral とし、各引数と族の body は既存の compatible reduction に従う。
恒等性は provability によって利用し、conversion は transport の構造と引数の定義的等価性を比較する。
閉じた集合値でも transport が neutral な評価結果として残るため、帰納型の constructor を得る評価と、元との等式を証明する操作を文書で区別する。

## 表面構文

既存の `\idelim` の族の sort を `\Prop` と `\Set(i)` に拡張する。
恒等則の証明を返す構文として `\transporteq` を追加する。

```text
\module Transport(A: \Set, F: A -> \Set, a, b: A) {
  \definition cast(value: F a)(same: a = b): F b :=
    \idelim a = b \with x: _ => F x
    \by { base: value, equality: same };

  \definition selfCast(value: F a)(same: a = a): F a :=
    \idelim a = a \with x: _ => F x
    \by { base: value, equality: same };

  \definition identity: \forall (value: F a)(same: a = a) -> selfCast value same = value :=
    \fun (value: F a)(same: a = a) =>
      \transporteq a \with x: _ => F x \by { base: value };
}
```

`\transporteq` は添字、添字の型、族の body、元を受け取り、自己移送と元との等式を証明する。
添字の型の `_` は既存の metavariable 推論を使う。
この例を import のない単独ファイルとして playground と CLI で検査する。

集合値を返す構成の等式仮定は、上の `cast` のような contextual な定義引数に置く。
移送の法則は、等式仮定を含む命題全体を `\forall` で量化して公開する。

## Kernel の表現と検査

共通項の `Node::IdElim` を、命題値と集合値を返す等式除去の表現として使う。
族の body を表す `predicate` は `family` に整理し、対応する AST、HIR、source view、表示でも同じ名称を使う。
kernel の `var`、`ty`、`left`、`right`、`family`、`base`、`equality` は、族の局所 binder と検査用の証明を保持する。
`Node::TransportEq` は `var`、`ty`、`index`、`family`、`base` を持ち、自己移送の恒等則の導出を表す。

`check.rs` の `IdElim` では、添字の型と両端点、binder の下での族の形成、始点に代入した型の元、両端点の等式証明を検査する。
族の形成結果に `BaseSort::Prop` または `BaseSort::Set(j)` を要求し、終点を代入した型を返す。
未確定の sort は既存の solver の保留制約へ渡し、宣言登録時の `finish` で確定させる。

`TransportEq` では添字、集合値の族、元を同じ検査経路で検査する。
左辺を `IdElim`、右辺を `base` とする等式を返し、左辺の検査用証明には `IdRefl(index)` を構成する。
族の形成と始点・終点への代入を共通 helper にまとめ、二つのノードの型規則を揃える。

`calculus.rs` の `comparison_children` では `IdElim.equality` を検査済みの証明として比較対象から消去する。
通常の child traversal は証明を含む全引数を辿り、shift、代入、occurs check、未解決 metavariable の検出、直列化には証明も含める。
conversion と unification は同じ比較対象を使い、異なる等式証明で構成した移送を定義的に等価とする。
比較対象からの消去と証明の検査を分離し、証明中の穴や型違いは既存の厳密な検査で検出する。

`Node::IdElim` と `Node::TransportEq` の子の順序と binder depth を `syntax.rs` の共通 traversal に登録する。
`skeleton`、alpha 等価性、source view と kernel 間の往復、共有 arena の整理にも同じ情報を使う。
`reduction.rs` と `Environment::erased_head` は、transport の構造を保持した head を返す。
適用、射影、case、induction はこの neutral な値を通常の項として受け取る。

## 構文解析と Elaboration

`src/syntax` の keyword、AST、parser、visitor に `\transporteq` を追加する。
`src/resolve` の HIR、lowering、binder の解決、macro template の走査に族の binder を反映する。
構文の情報を LSP、playground、docs の keyword 表示にも反映する。

`src/elaboration/src/raw/exp.rs` の `Prove::IdElim` を `ExpNode::IdElim` に移し、返す値の sort を kernel の検査で決める。
`TransportEq` は provability の導出として `Prove` に追加する。
`elaborator/term_elaborator.rs`、`lowering/logical.rs`、raw と kernel 間の変換、printing、diagnostics の対応を揃える。
module parameter の捕捉、具体化、置換でも族の body の binder と外側の引数を区別する。

診断には族の sort、`base` の期待型、要求する等式を表示する。
反対向きの等式、異なる添字の型、元の型違いをそれぞれ検査位置に対応させる。

## 標準ライブラリの法則

`std.Logic.Equality` の下に集合値の移送を扱う `Transport` module を追加する。
添字の集合と集合値の族を parameter とし、contextual な移送関数と、恒等、合成、往復、定数族の法則を公開する。
別の族と依存する写像を受け取る子 module で自然性を証明する。
各 law は元、添字、等式仮定を命題全体で量化する。

\(T_F(a,b,u)\) を移送の略記として、次を証明する。

\[
\begin{aligned}
T_F(a,a,u)&=u,\\
T_F(b,c,T_F(a,b,u))&=T_F(a,c,u),\\
T_F(b,a,T_F(a,b,u))&=u,\\
T_{x\mapsto C}(a,b,u)&=u,\\
T_G(a,b,f(a,u))&=f(b,T_F(a,b,u)).
\end{aligned}
\]

各式の形成に必要な添字の等式を仮定し、自然性では \(f:\Pi x:A.\,F x\to G x\) を使う。
恒等則は `\transporteq`、残りは既存の命題値の `\idelim` と等式の推移律から証明する。

合成則で終点を \(x\) に動かす述語は、\(b=x\) を含意の仮定に持たせる。
その仮定と \(a=b\) から両側の移送を型付けし、\(x=b\) の場合を恒等則で示す。
定数族と自然性にも同じ方法を使う。
証明の導出が異なる場合の移送の一致は、検査用証明を消去する conversion と `\refl` で確認する。

## 微分形式への適用

`Euclidean/On/Regrade.ref` と `Forms/On/Regrade.ref` の `cast` を、`Form` を族とする `\idelim` へ置き換える。
`RegradeIdentity.law` は原始の恒等則から証明し、次数を二段階で変更する合成則も公開する。

Euclidean の `convert` は任意の次数へ成分を抽出する構成として保持する。
`convert` の自己次数での恒等性を表示の復元から証明し、等しい次数では `cast omega same = convert omega` を命題値の等式除去で示す。
この橋渡しから `series`、`evaluation` と既存の成分に関する法則を得る。
加法、スカラー倍、偏微分、制限、引き戻しとの整合性は、移送の自然性またはこの橋渡しを使って証明する。

大域形式では chart ごとの移送と全体の移送の一致を証明し、`family` と `compatible` を使う利用側を接続する。
`Pair.Regrade`、restriction、pullback、`Forms.On.DeRham.Regrade` まで新しい `cast` の意味を通す。
外積、単位則、結合則、次数付き可換則、Leibniz 則、外微分、De Rham の積の証明を、新しい移送の等式で検査する。
成分の計算に使うリスト表示と、等しい次数間の受け渡しを担う transport の役割を整理する。

## 体系の文書と意味付け

`system.md` と `props/sorted-calculus.md` に構文、binder、型規則、恒等則を追加する。
分類付き体系では集合値の transport を集合値の構文 family に配置し、命題値の等式除去との分類を保つ。

集合モデルと型コードモデルでは、transport の値を入力の元の値として解釈する。
型規則の等式前提から両端点の解釈の一致を得て、族の代入による終点の型への所属を示す。
恒等則の解釈は同じ集合値同士の等式となる。

`props/` の代入、generation、subject reduction、合流性、証明消去、意味保存の証明を拡張する。
transport の内側の簡約には引数と族に対する帰納法を使う。
型コードモデルへの追加は raw 項の全域的な解釈として記述し、型付け導出への依存を避ける。
現在の共通項から分類付き補助体系への移送義務との関係を `props/props.md` と `props/proof.md` に反映する。

## 実装手順

1. 体系の規則と表面構文を文書に反映し、集合値の移送と恒等則の最小例を用意する。
2. kernel の `IdElim` の検査を拡張し、`TransportEq`、比較時の証明消去、binder の traversal、共有と直列化を実装する。
3. syntax、resolve、raw の分類、elaboration、診断、エディタの表示を接続する。
4. kernel と表面構文の検証を通し、標準ライブラリの法則を証明する。
5. Euclidean と大域形式の `Regrade.cast` を移行し、既存の表示との橋渡しと利用側の定理を検査する。
6. メタ理論の文書、G12 の比較例、永続キャッシュの再利用を更新し、下記の完了条件を満たす。

## 検証と完了条件

kernel の直接テストでは、集合値と命題値の消去、異なる集合の level、部分集合型を値域に持つ族、nested binder の代入を検査する。
恒等則の等式の型と、transport の neutral な head を確認する。
異なる等式証明の移送の conversion と unification、および証明内に未解決の穴がある場合の登録失敗を確認する。
`base` の型が始点の型と異なる場合、等式の向きが違う場合、許されない sort の族を指定した場合を検査する。

表面構文のテストでは、型の `_`、module の具体化、macro 内の族の binder、移送を関数適用・射影・induction の対象にする例を検査する。
標準ライブラリの合成則と自然性を、等式仮定を含む述語による消去の検証として使う。
G12 の最小例と現在の表示による対照例を、それぞれ 100 行以内で playground に貼り付けられる独立したファイルとして `fix-md/cases/` に置き、`fix-md/README.md` と `gaps.md` に結果を反映する。

変更した crate の検査から始め、関連チェックが通った後に workspace のテストと clippy を実行する。

```sh
cargo test --workspace --locked --offline
cargo clippy --workspace --all-targets --locked --offline -- -D warnings
cargo run -p cli --release --locked --offline -- libs/std --full-check-local
cargo run -p cli --release --locked --offline -- libs/differential_forms --module differential_forms --full-check-local
cargo run -p cli --release --locked --offline -- tests/projects/manifolds-de-rham --module manifolds_de_rham_tests --cache-stats
```

ライブラリの検査は既存の依存キャッシュを再利用し、変更した package を `--full-check-local` で検証する。
`sema/build.rs` の checker fingerprint に変更した Rust の実装が含まれることを確認し、新しい項を含む checkpoint を保存・復元して別プロセスで再検査する。
型判断・whnf・conversion・代入の既存キャッシュを通し、証明の比較対象からの消去後も検査義務を保持する。

集合値の移送、恒等則、合成則、自然性が検査でき、微分形式の次数変更と既存の定理が新しい `cast` で成功することを実装完了とする。
