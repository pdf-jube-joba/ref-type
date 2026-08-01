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

##  quick sort

## ユークリッド互除法

## McCarthy91 function

# 参考になりそうな話
- later modality や guarded recursion
  - 普通の fixpoint じゃなくて \((\triangle A \to A) \to A\) みたいな lob theorem っぽいものにする
- CBPV とか generator として closure を返す
- Bove-Capretta 法
