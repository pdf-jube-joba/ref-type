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
nested recursion な例
```
rec n =
  if (n > 100) then (n - 10) else rec (rec (x + 11))
```

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
## next っぽさ？
CBPV や coroutine のように、"次に計算するべき項"がわかるようにする。
`\next \fix f M -> M[f = \fix f M]` のように、 next 一個で reduction を一個進めることにして、
`\eventually \fix f M` は停止性が証明できた時だけ使える。

時相論理とかになりそう。
later modality の話では型レベルに入れてて stream 型みたいなものに対して行ってた。
型としても `Notyet A` みたいなのを導入して、内部の fixpoint はそれに包まれるようにする。
ここでも force とか eventually みたいなので完全に reduction を与えたい。
nested がちょっと大変なので、 value/computation を分ける形にして、
計算順序をかなりしっかり指定できるとよさそうという。

型 `A` を `Notyet A` に coersion して、 fixpoint が全体で `Notyet Notyet ... A` になる？
また、単に nested recursion に対しては計算順序をちゃんと指定することで、普通の nest が書けないようにする。

higher なものはよくわからない。
