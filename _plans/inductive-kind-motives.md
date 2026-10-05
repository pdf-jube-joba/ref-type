<a id="g12"></a>

# G12: 開いた motive による帰納型の消去

実装済み。
`IndElim` の motive を telescope と本体に分け、表面構文を `\induction` に統一した。
G12 は [`gaps.md`](gaps.md) から分割した項目である。
再現例と調査の経緯は [調査報告 G12](fix-md/README.md#g12) を参照。

## 型検査と表現

`IndElim.motive_bindings` は添字と要素の束縛変数列、`IndElim.motive` はその文脈にある型の本体である。
elaboration の raw 表現も同じ束縛構造を持つ。
型検査では帰納型の arity から telescope の期待型を求め、各 domain を照合した文脈で本体の formation を検査する。
前提は \(\Gamma,\vec i:\vec I,x:D\,\vec i\vdash P:s\) であり、結果型は \(P[\vec j/\vec i,t/x]\) になる。
constructor の枝と再帰仮定の型も同じ本体への代入で構成する。

```text
\definition Valid: Nat -> \Prop :=
  \induction (n: Nat) \return \Prop \with {
    | zero: Nat::zero = Nat::zero
    | succ: \fun (n: _) (previous: \Prop) => previous
  };
```

`P := Prop` と `P := Real -> Real -> Prop` は `PropKind` に分類される。
それぞれ命題、実数上の二項述語を構成する帰納法になる。
通常の motive ラムダの型形成は upper sort の classifier を要求するが、本体の formation はその文脈内で成立する。
変更前の自然数の例は `Sort` → `Product` → `Lambda` の経路で `upper sort has no classifier` となることを確認した。

## 表面構文と elaboration

```text
\induction (n: Nat) (xs: Vec[A] n) \return P n xs \with {
  | nil: base
  | cons: step
}
```

elaborator は binder の文脈で本体を elaboration し、枝を外側の文脈で elaboration する。
添字と要素を受け取る外側のラムダの中に `IndElim` を直接生成する。
motive と枝を引数として受け取る汎用 recursor の生成は廃止した。
`prec` の構文、AST/HIR の variant、名前解決と elaboration の経路も削除した。
既存ライブラリとテストの用途は constructor 名付きの枝へ移した。
`libs/integration/src/Real/Division.ref` の `Valid` は `Real -> Real -> Prop` への直接の再帰を使う。

添字付き帰納型の検証で、宣言時の添字文脈が constructor の文脈へ漏れる問題と、正値性検査が添字への適用を負の出現として扱う問題も修正した。
添字と parameter の中の再帰的出現は正値性検査で検出する。

## 束縛、代入、簡約

kernel の共通構文走査は telescope の各 domain を先行 binder 数、本体を telescope 長の下で扱う。
shift、同時代入、自由変数、metavariable の走査はこの規則を共有する。
conversion の構造比較では motive の変数名を消去し、telescope 長と子の束縛深さを保持する。
elaboration の module parameter の代入・宣言参照の変換にも同じ束縛深さを適用した。
単一化では比較対象の domain または本体に対応する telescope の prefix を文脈へ追加する。
constructor への簡約は各再帰引数に同じ開いた motive の消去式を作り、枝に帰納仮定として渡す。
共有構文の永続化形式の変更に合わせて semantic cache の schema を更新した。

## 許可範囲と整合性の検討

消去元と本体の sort の許可条件は [kernel の仕様](../src/kernel/README.md) に記載した。
今回の表現変更は従来の kernel が明示ラムダから取り出していた telescope と本体を直接格納するものであり、受理されていた直接の kernel 消去と対応する。
`Set(i)` から `PropKind` への消去は従来の kernel の許可条件であり、通常の表面構文からも到達できるようになった。
命題値の族は、constructor ごとに命題を与え、再帰的な位置に同じ族の結果を渡す構造再帰として扱われる。
枝の本体と帰納仮定の型は同じ motive への代入で得るため、通常の積と代入の規則で検査する。

upper sort の分類規則、積の非可述性、帰納型の universe 条件は既存の規則を使う。
命題の帰納型からの大きな消去には既存の singleton 条件が適用される。
型や命題を field に持つ structure の射影も、この条件と通常の field 型の形成を経由する。
これらは実装上の規則の対応と型保存の確認であり、singleton 条件や非可述な積を含む体系全体の整合性証明とは区別する。

## 検証

- `tests/ok/inductive/open_motives.ref`: 命題、述語、外側の変数、parameter と添字を持つ再帰、依存する結果型、関数を介した再帰仮定、constructor の計算規則。
- kernel テスト: telescope の shift・代入・自由変数・alpha 同値、sort の許可と拒否、singleton 条件、簡約前後の型保存。
- `tests/ng/inductive_motive_large_elimination.ref` と `inductive_motive_telescope.ref`: 許可されない大きな消去と不完全な telescope。
- G12 の三つの再現・対照例と `kernel_probe.py`。
- `cargo test --workspace --no-fail-fast`: 314 テスト成功、失敗・無視ともに0。積分・category を含むライブラリの検証も成功。
- `cargo fmt --all --check` と `git diff --check`: 成功。
