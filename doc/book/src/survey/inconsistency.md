inconsistency とは次のことを言う。
> どんな型 $\Gamma \vdash T: s$ に対しても、ある項 $t$ であって $\Gamma \vdash t: T$ となるものがある。

このとき、証明体系としてはなんでも示せる体系となっていて価値がない。
ただ、 $\forall P: \text{proposition}. P$ がエンコードできるような体系なら、 inconsistency はだいたい、この型が項を持たないことに帰着する。次のように定義しておく。
- $\bot_s := (p: s) \to p$
- $\neg_s := \lambda (p: s). p \to \bot_s$

目標は、 $\bot_s$ が項を持たないような Proposition を表す sort があること。

# PTS との関連
一般の PTS を考える。
以下はここだけの定義（こうよんでも別に間違いではないはず。）
- $s \in \mathcal{S}$ が impredicative $\Leftrightarrow$ $(s, s') \in \mathcal{A}, (s', s, s) \in \mathcal{R}$
  - このとき、 $\bot_s: s$ である。
- proposition に対応する sort を決めている場合には単に $bot$ と書くだろう。

## type in type
有名な話として、 $\text{Type}: \text{Type}$ だと矛盾するらしい。
PTS なら、 $s \in \mathcal{S}$ であって $(s: s) \in \mathcal{A}$, $(s, s) \in \mathcal{R}$ となるものがあると矛盾する。
MLTT の一番最初のものはこれでだめだとわかったらしい。
（Girard's paradox）
system $U^-$ から翻訳して矛盾が見つけられる。

## impredicative sort
PTS として、なにかしら $s_1: s_2$ のようになっているとき、
$(s_2, s_1) \in \mathcal{R}$ なら $(\Pi x: s_1. s_1 -> s_1): s_1$ となるから $s_1$ は impredicative な sort である。
このような sort は hierarchy の一番下でなければいけない。
つまり、 $(\exists s_0): s_1$ になっているだけでだめ？
よくわからなかった。
これは system $U^-$ の失敗と同じ。
system $U^-$ だけみると、 $(\exists s_0): s_1$ だけでは矛盾するとは限らなそうだが。
ただ、ほかのと合わせ技で辛そう。
これも多分 system $U^-$ から翻訳してわかるのでよい。

## system $U^-$
次に、 System $U$ と $U^-$ もあり、どっちも inconsistent である。
System $U$ は PTS で次のように定義する。
- $\mathcal{S} = \{*, \square, \triangle\}$
- $\mathcal{A} = *: \square, \square: \triangle$
- $\mathcal{R} = {(*, *), (\square, \square), (\square, *), (\triangle, *), (\triangle, \square)}$
System $U^-$ はここから $(\triangle, *)$ を抜く。

$s_1: s_2$ という階層として $*: \square: \triangle$ となっているが、
一番下の $*$ は impredicative でもよいが、 $\square$ も impredicative なのがまずいらしい。

## retract について
次のコンテキストは矛盾する。
```
Assum b: PROP
Assum i: b -> PROP
Assum o: PROP -> b
Assum h_1: (p: PROP) -> p -> i o p
Assum h_2: (p: PROP) -> i o p -> p
```

これが成り立ってしまうような $b$ のことを retract という。
大きい universe を小さい universe に埋め込もうとすると変になる、ということ。

特に、 $*_p$ と $"bool"$ を同一視するとか、べき集合を $A -> \square$ で表して $\Pi A: \square. (A -> \square)$ のようなべき操作をとるとか、

## dependent sum
$A \times B$ の拡張として、 $x: A$ に依存して決まる $B(x)$ があるときに $x: A$ と $y: B(x)$ の組をペアにすることができそうだ。
これが依存和になる。
項を次のように拡張する。
- $\Sigma \mathcal{V}: t. t$ ... 依存和の型
- $(t, t)$ ... 依存和の項

dependent sum は elim に対応する項の作り方がいくつかある。

| category | conclusion | premises |
| --- | --- | --- |
| dep.sum intro | $\Gamma \vdash (\Sigma x: T. T): s_3$ | $\Gamma \vdash T: s_1, \Gamma :: x: T \vdash T' : s_2$ |
| dep.sum form | $\Gamma \vdash (t_1, t_2): (\Sigma x: T. T')$ | $\Gamma \vdash t_1: T, \Gamma \vdash t_2: T'[x := t_2]$ |

ここの $(s_1, s_2, s_3)$ でなにを許すかが問題になる。
ここで impredicative + strong dependent sum にすると矛盾する。

### strong dependent sum
elim として projection を $2$ つ用意するのが strong dependent sum になる。
項としては $\pi_1 t$ と $\pi_2 t$ を導入し、 $\pi_i (t_1, t_2) \to^\beta t_i$ を reduction として導入する。

| category | conclusion | premises |
| --- | --- | --- |
| dep.sum elim1 | $\Gamma \vdash \pi_1 t: T$ | $\Gamma \vdash t: (\Sigma x: T. T')$ |
| dep.sum elim2 | $\Gamma \vdash \pi_2 t: T'[x := \pi_1 t]$ | $\Gamma \vdash t: (\Sigma x: T. T')$ |

Luo の ECC で述べられているところによると、
1. $(s_1, s_2, s_3) = (square, *, *)$ をやると矛盾する。
2. $(s_1, s_2, s_3) = (*, *, *)$ は矛盾しない。
3. $(s_1, s_2, s_3) = (square_i, square_j, square_(max(i,j)))$ みたいなものは矛盾しない。

Coq での対応する帰納型を定義してみる。
```
Inductive sig: (A : s1) ->  (P : A -> s2) -> s3 :=
  ex : (A: s1) -> (P : A -> s2) ->  (t1 : A) -> (t2: P x) -> sig A P.
```
Coq では $(s_1, s_2, s_3) = ("Type", PP, PP)$ でも問題なく定義ができる。
ただし、 $pi_1$ や $pi_2$ に関して、無条件に型を付けることはできない。
これは elim 時に、 Prop を分解していいのは Prop の項を作るときだけという制限がかかるためである。
（ large elimination ）
```Coq
Fail Definition projection1: forall (A: Type), forall (P: A -> Prop), sig A P -> A :=
  fun (A: Type) => fun (P: A -> Prop) => fun(x: sig A P) =>
  match x with
  | ex _ _ x y => x
  end.
```
>  Incorrect elimination of "x" in the inductive type "sig":
  the return type has sort "Type" while it should be "SProp" or "Prop".
> Elimination of an inductive object of sort Prop is not allowed on a predicate in sort Type
> because proofs can be eliminated only to build proofs.

### weak dependent sum
dependent sum を dependent sum なしの体系で再現しようとすると、 $pi_2$ はうまく作れない。
逆に言うと、 dependent sum を $pi_2$ だけ除いたようなやつは適当にやっても矛盾しなさそう。
$\Sigma x: T. T' := \Pi R: *_p. (\Pi X: T. T' -> R) -> R$ みたいな感じでやる。

つまり、 $\pi_2 (e)$ を用いて $\pi_1 (e)$ が $B$ を満たすことを証明できるような状況になっていると多分矛盾する？
$(s_1, s_2, s_3) = (\square, *, \square)$ なら矛盾はしないと思うが。
