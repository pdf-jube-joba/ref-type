# 動機
普通の再帰を書くのは体系的には許しがたくて、構造再帰に帰着させないといけない。
再帰関数の作り方は recursor によるものと match で引数が減るものがある。

## Accesiblity
```
fix A: Type;
fix R: (A: Type) -> (A: Type) -> Prop;

indutive Acc (x: A) : Prop :=
acc: ((y: A) ->  R y x -> Acc y) -> Acc x; 
```

# 気にしておくべき例

## Acc に簡単に帰着できる例
普通に構造再帰になっていない例

quick sort
```
rec xs =
  match xs with
  | Nil => Nil
  | Cons x xs =>
      let less = filter (x > _) xs;
      let more = filter (x < _) xs;
      less ++ [x] ++ more
```

これを Acc にするには、 length が減ってる証拠だけ渡せばいい。

ユークリッド互除法も同じ。

こういう単純なものの場合は、 Bove-Capretta 法で割と自動で停止性用の命題を出せるらしい。

## nested recursion
nested recursion な例 (McCarthy 91 function)
```
\rec[f] n =
  if (n > 100) then (n - 10) else f (f (x + 11))
```

- すべての $n$ に対して、 functional relation としての存在はわかる。
- CBV を仮定して、 rewriting system としての停止性が示せれば、正規の項として導入可能とか？
  - rewriting system をそのまま内部で表現できるか？

later modality の導入論文で停止性っぽいものを自動で導出している。

## higher order な例
higher order とか partial application が入る例

```rose map
Inductive rose (A : Type) :=
| node : A -> list (rose A) -> rose A.

Fixpoint rose_map {A B} (f : A -> B) (t : rose A) : rose B :=
  match t with
  | node x ts =>
      node (f x) (map (rose_map f) ts)
  end.
```

# 参考になりそうな話
- later modality や guarded recursion
  - 普通の fixpoint じゃなくて \((\triangle A \to A) \to A\) みたいな lob theorem っぽいものにする
- CBPV とか generator として closure を返す
- Bove-Capretta 法

# 考えたこと
CBPV や coroutine のように、"次に計算するべき項"がわかるようにする。
次に計算するべき項の列が計算できることが証明できるなら、それを実際に最後まで計算していい。

## next っぽさ？
> [!Note]
> 時相論理で出てくる next は、 `A -> |> A` の型を持っている。
> この next はどちらかというと constructor っぽい。
> 今考えているのは逆で fix に対する eliminator っぽいので名前を変えて step にする。

`\step \fix f M -> M[f = \fix f M]` のように、 `\step` 1個で fix に対する reduction を行える。
`\eventually \fix f M` は停止性が証明できた時だけ使えて、出てきた全ての fix に `\step` を与えたのと同じ効果にする？

時相論理とかになりそう。
later modality の話では型レベルに入れてて stream 型みたいなものに対して行ってた。
型としても `Notyet A` みたいなのを導入して、内部の fixpoint はそれに包まれるようにする。
ここでも force とか eventually みたいなので完全に reduction を与えたい。
nested がちょっと大変なので、 value/computation を分ける形にして、
計算順序をかなりしっかり指定できるとよさそうという。

型 `A` を `Notyet A` に coersion して、 fixpoint が全体で `Notyet Notyet ... A` になる？
また、単に nested recursion に対しては計算順序をちゃんと指定することで、普通の nest が書けないようにする。

higher なものはよくわからない。

## step っぽい遷移系に対する reduction ?
呼び出しに対する configuration `A` があったとして、
自由に再帰的な関数 `f: A -> B` を定義する代わりに、
もし計算が終了しなかった場合に次に呼び出すための `A` をくっつけた
`f: A -> A + B` の形で定義したとして、
型 `B` になるまで `f` を与え続ける fuel 付き（切れたら panic）操作を考える。
```
f' (n: N) (a: A): B :=
match n with
| Z => panic!()
| S n' =>
  match f a with
  | Left a' => f' n' a'
  | Right b => b
```
これに対して、無限に大きい fuel を実は与えていたと考える？
有限回の適用で `B` に行くことが示せるなら `f (a: A)` から `B` を得てもよい。

CBPV だと `A` は Compute 側で `B` は Value 側なので、 `A + B` を書くのは微妙？
やりたいことは `Compute(B) -> Compute(B) + Value(B)` から `Value(B)` を取り出すことではあるが、型付けとその経緯のことを考えると微妙。

\(X_0 := f^{-1} B, X_n := f^{-1} X_{n-1}\) に対して、 \(\exists n: N, a \in X_n\) から \(B\) を得ていて、これは Prop 側の条件。

Compute sort 側で `f: A -> A + B` があったときに、
- `quote(f): comp(A -> A + B): Set`
  - `quote` と `comp` は、 constructs と可換にする。つまり、 `quote(\lambda x:A, B) = \lambda x: quote(A), quote(B)` のような感じ。
  - **これはもともとの Rf に対応する奴**
- `Rel(f, a, a') := (f a = Right a')`
- `terminates(f, a) := \exists n: N, \exists b: B, is_right (f' n' a): Prop`
- `run(f, a): B: Compute` で one-step reduction で `match f a with | Left a' => run(f, a') | Right b => b` とする。

> [!note]
> ところで、 context に false が入ると type check が停止しなくなる。
> （CoC ではどれだけ context が嘘でも、 strong normalization だけは成り立っている。）
> これは一旦 **許容する** ことにする。
> まずは型システムに組み込めなければいけないので、その点を考慮するべき。
> なお、 `run(f, a)` も reduction 単体では停止しない可能性があるが、これは ill-typed な CoC の term が停止しないことがあるのと同じなので考えなくていいはず。

`f'` を使う必要はなさそう。
```
inductive terminates(f: A -> A + B): A -> Prop :=
| End : (a: A) -> \exists (b: B) -> f a = Right b -> terminates(f, a)
| Step: (a: A) -> \exists (a': A) -> f a = Left a' -> terminates(f, a') -> terminates(f, a)
```

> [!note]
> これは Acc を普通に使っていいらしい
```coq
Inductive Acc (A: Type) (R: A -> A -> Prop): A -> Prop :=
| acc: forall (x: A), (forall (y: A),  R y x -> Acc A R y) -> Acc A R x.

Variable A B : Type.
Variable f: A -> A + B.

Definition Rel (x: A) (y: A): Prop := f y = inl x.
Definition Ac := Acc A Rel.

Inductive Terminate: A -> Prop :=
| End: forall a: A, forall b: B, f a = inr b -> Terminate a
| Step: forall a1 a2: A, Terminate a2 -> f a1 = inl a2 -> Terminate a1.

Theorem term_to_acc: forall a: A, Terminate a -> Ac a.
Proof.
intros a h.
induction h as [a b H | a a2 h IHh].
-
constructor. intros y nev. unfold Rel in nev.
rewrite H in nev. discriminate nev.

-
constructor. intros y step. unfold Rel in step.
assert (y = a2) by congruence.
subst y. clear H step.
unfold Ac in IHh. exact IHh.

Qed.
```

Acc がすでに transitive closure っぽさをもっているので、 Rel の trans cl. をとらなくていい。

```
Theorem acc_to_term: forall a: A, Ac a -> Terminate a.
Proof.
intros a h.
induction h as [a _ Ih].
destruct (f a) as [a2 | b] eqn: h.
-
refine (Step a a2 _ h).
apply Ih. exact h.
-
eapply (End a b h).
Qed.
```

> [!note]
> 一般には acc は無限降下列がないことの構成的な証明らしい。
> なので、 step よりも acc の方がある意味では強いが、今回の定式化だと同値になった。
> ところで、 encoding ではこうなる：
> ```
> Acc A R := (P : A -> Prop) -> ((x: A) -> ((y: A) -> R y x -> P y) -> P x) -> P x
> ```
> これを生で書けば項は削減できる。
> 同様の方向で、 Sum についても削減はできるかもしれないので、
> 体系としてちゃんと定義できた後にやりたい。
