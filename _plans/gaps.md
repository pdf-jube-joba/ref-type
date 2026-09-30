## record eta 則
record に対する eta がない。 `s = { fiel1 := 2 #field }` が示せない。

## 一意選択の結果型の推論
`\take` の本体と `\takeelim` の関数を、指定された結果型で検査してほしい。
例えば `g: \Cast[Nat^] (GcdSet a b)` から `Nat^` を返す場合、`\take (g: \Cast[Nat^] (GcdSet a b)) => g` と書きたい。
現在は `g` の refinement type が結果型として推論されるため、`(\fun (n: Nat^) => n) g` で結果型を指定している。
