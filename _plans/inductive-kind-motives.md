>  ## 帰納型の再帰的な述語
>
>  帰納型の再帰を使って、命題値の述語を直接定義したい。
>
>  ```text
>  \definition Valid(tags: Tags) (a, b: Real): \Prop :=
>    \prec[Tags, \fun (tags: Tags) => Real -> Real -> \Prop]
>      (\fun (x, a, b: Real) => Logic.And[Le a x, Le x b])
>      (\fun (left: Tags) (leftValid: Real -> Real -> \Prop)
>        (right: Tags) (rightValid: Real -> Real -> \Prop) (a, b: Real) =>
>        Logic.And[leftValid a (midpoint a b), rightValid (midpoint a b) b]) tags a b;
>  ```
>
>  現在の recursor はこの motive を `upper sort has no classifier` として拒否する。
>  積分のタグ付き分割では、`Real -> \Pow Real` に対する再帰で適切なタグの集合を作り、所属命題から `Valid` を定義している。

# Upper sort に分類される motive と帰納型の消去

## 検討する規則

帰納型 `Ind` と、文脈内での判断 \(\Gamma,x:\mathrm{Ind}\vdash P:\PropKind\) があるとき、`P` を return に置いた帰納法を許すことを検討する。
scrutinee を \(t:\mathrm{Ind}\) とすると、枝が適切に型付けされる場合、結果の型は \(P[t/x]\) になる。

```text
\induction (x: Ind) \return P \with {
  | constructor : branch
}
```

この記法の `x` は motive の束縛変数であり、結果は適用先の scrutinee に依存する。
上の例は constructor と branch を省略した模式例である。
添字付き帰納型では、添字と帰納型の要素を合わせた telescope の下で `P` を検査する。

## 命題、述語の型、motive の区別

次の二つは分類が異なる。

```text
Logic.And[Le a x, Le x b] : \Prop
Real -> Real -> \Prop : \PropKind
```

前者は命題であり、後者は命題値の関数を分類する型である。
`P := Real -> Real -> \Prop` とした帰納法の結果は、`Real -> Real -> \Prop` 型の述語になる。
`P := \Prop` とした帰納法の結果は、`\Prop` 型の命題になる。
どちらも motive の本体は `\PropKind` に分類される。
一方、`P` 自体が命題で \(P:\Prop\) なら、帰納法の結果は `P` の証明になる。

枝のラムダと motive のラムダも区別する必要がある。

```text
\fun (x, a, b: Real) => Logic.And[Le a x, Le x b]
  : Real -> Real -> Real -> \Prop

\fun (tags: Tags) => Real -> Real -> \Prop
  : \forall (tags: Tags) -> \PropKind
```

枝のラムダの型は `\PropKind` に分類されるため、通常の積の形成規則で扱える。
motive のラムダについては、その型の形成に `\PropKind` の classifier が必要になる。
現在の体系では upper sort に classifier がなく、通常のラムダとしての型付けはここで成立しない。

## Motive を開いた型の族として扱う

消去規則の前提を \(\Gamma,x:\mathrm{Ind}\vdash P:s\) として直接与えれば、motive 全体を通常の関数項として型付けする必要はない。
必要なのは、束縛変数の型が正しく、本体 `P` が許可された sort `s` に分類されることである。
`s = \PropKind` でも、この前提自体は upper sort の classifier を要求しない。

たとえば、自然数の帰納法を使って命題を作る次の式が候補になる。

```text
\induction (n: N.Nat^) \return \Prop \with {
  | zero: Q
  | succ: \fun (n: _) (previous: \Prop) => Logic.And[Q, previous]
}
```

ここで `Q: \Prop` とする。
結果は自然数に対応する命題であり、再帰結果 `previous` も命題である。
constructor における motive の代入結果を枝の期待型にし、再帰的な引数については同じ motive から再帰結果の型を作る。

この設計では、motive を消去式の内部で束縛された構文として保持する。
通常の application を経由せず、scrutinee や constructor を motive の本体へ代入することで結果の型を得る。
本体の型付け、代入による型付けの保存、枝への簡約による型の保存が必要になる。

## 現在の kernel との対応

[`inductive_elimination`](../src/kernel/src/check.rs) は、明示された pure lambda を引数列と本体へ分解している。
引数列を帰納型の添字と要素の型に照合し、その文脈で `formation(motive.body)` を呼ぶ。
motive 全体への通常の `infer_open` は、この分解ができた場合には呼ばれない。
lambda が明示されていない場合は、通常の型推論から引数列を取り出す経路を使う。

現在の許可条件には、`Set(i)` の帰納型から `PropKind` への消去が含まれる。
したがって、上記の案の中心部分は既に kernel に存在する。
[`motive_type`](../src/kernel/src/check.rs) も lambda を剥がして検査するが、現在の呼び出し先は step match であり、帰納型の消去とは別の経路である。

一方、[`elaborator`](../src/elaboration/src/elaborator/term_elaborator.rs) は `\induction` と `\prec` の両方で motive を通常の lambda として型推論している。
さらに、`primitive_recursion` で motive、枝、scrutinee を受け取る関数を生成し、motive と枝を適用する。
この経路では、kernel の消去規則による特別扱いに到達する前に、upper sort を返す motive の型付けが問題になる。
[`gaps.md` の「帰納型の再帰的な述語」](gaps.md#帰納型の再帰的な述語)の例については、この経路と実際のエラーの対応を実行して確認する。

## Kernel の表現と表面構文の統一

kernel の motive は、通常の lambda 項の代わりに、束縛変数 `(x: A)` とその文脈内の本体 `P` の組で保持する案とする。
添字付き帰納型では、束縛変数の telescope と本体の組へ一般化する。
型検査時に lambda を剥がす方式から、構文自体が型の族の束縛構造を表す方式へ揃える。
代入、shift、自由変数の検査、conversion、簡約は、この束縛構造に対応させる。

表面構文は `\induction` に統一し、`\prec` の用途を constructor 名付きの枝へ移す案とする。
現在の関数値を返す `\induction` は、scrutinee を受け取る外側の lambda と、motive と枝を直接持つ kernel の `IndElim` に変換する。
この外側の lambda は、motive を関数項として包装する lambda とは役割が異なる。
motive と枝を引数に取る汎用 recursor の生成を経由せず、開いた文脈の本体 `P` を直接検査する。

## Upper sort の分類と整合性

この消去規則は `\PropKind` に classifier を追加しない。
motive の本体を開いた文脈で検査する規則と、`\PropKind` を通常の型として分類する規則は分けて考える必要がある。
今回の述語の構成だけから System U を得るとはいえない。

ただし、motive の扱いを整理するだけで体系全体の整合性が証明されるわけではない。
消去元の sort、許可する消去先、帰納型の形成規則、積の非可述性を合わせて検討する必要がある。
特に、命題の帰納型からの消去に同じ許可を一律に広げる場合は、証明から命題や型を取り出す規則の強さを別途検討する。

`P := \Prop` の消去は、帰納型の要素に応じて命題を構成するため、type family を定義する機能になる。
`P := Real -> Real -> \Prop` の例も、帰納型の要素と実数の引数に応じて命題を構成する。
motive を束縛変数と本体の組に変えることは表現の整理だが、表面構文でこれらを通せるようにすることは利用可能な機能に関わる。
「通常の lambda として検査する必要がなくなった」という理由だけで消去先を広げると、組み合わせによって矛盾を導入する可能性がある。

整合性の検討では、次を確認する。

- 消去元と消去先の sort の組ごとの許可条件、および singleton elimination の条件。
- 帰納型の正値性と universe の条件、および再帰結果として命題や型を受け取る枝の型付け。
- 積の非可述性や、型・命題をデータとして包装して取り出す操作との組み合わせ。
- 開いた motive への代入の保存と、constructor に対する簡約の subject reduction。

型保存や個別の例の成功は、体系全体の整合性の証明とは区別する。
既存の体系への解釈などによって、許可する type family の範囲を正当化する必要がある。

## 方針案

kernel の motive を telescope と本体の組にし、表面構文を `\induction` に統一する方針を検討する。
`P: \PropKind` を許す条件を明示し、通常のラムダの型付けとの違いを仕様に記載する。
type family の形成として整合性を検討し、消去規則の許可範囲を確定する。
実装を変更する前に、現行の `Valid` の例と、命題を直接構成する自然数の例を確認する。
変更が必要なら、その結果に基づいて表面構文から kernel までの分類の扱いを揃える。
