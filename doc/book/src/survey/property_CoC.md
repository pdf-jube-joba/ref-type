一回、 CoC の性質についていろいろ証明を見ておく。

# confluence (Church-Rosser)
代入やα変換についてまじめに考える必要がある。
例： $\lambda x. y \equiv \lambda x'. y$ とみたいので、 $(\lambda x. y)[y := x]$ はそのまま計算すると具合が悪い。
こんな感じで、 free occurence に気を付ける必要がある。
以降では、α同値で項を同一視する。
これがつらい場合には、 de-Brujin index を用いること。
（定理証明支援系で示すとかの場合にはそれを使った方がいいかも。）

普通の $\beta$ reduction は次のような感じ

#def1
1. $\lambda x: A. t \to_\beta \lambda x: A'. t$ if $A \to_\beta A'$
2. $\lambda x: A. t \to_\beta \lambda x: A. t'$ if $t \to_\beta t'$
3. $(x: A) \to t \to_\beta (x: A') \to t$ if $A \to_\beta A'$
4. $(x: A) \to t \to_\beta (x: A) \to t'$ if $t \to_\beta t'$
5. $t_1 t_2 \to_\beta t_1' t_2$ if $t_1 \to_\beta t_1'$
6. $t_1 t_2 \to_\beta t_1 t_2'$ if $t_2 \to_\beta t_2'$
7. $(\lambda x: A. t_1) t_2 \to_\beta t_1[x := t_2]$
  - $t_2$ の FV が $x$ を含まないようにとれているとすることができる。

示したいのは、「 $t \to_\beta t_1$ かつ $t \to_\beta t_2$ ならば、 $t'$ があって $t_1 \to_\beta^* t'$ かつ $t_2 \to_beta^* t'$ が成り立つ。」である。
（この性質を合流性 (confluence) とか church-Rosser という。）


これを示すのに、 parallel reduction と呼ばれる別の簡約を定義して、
もとの簡約との関係を用いる方法がある。
（ Tait, Martin-L"of method ?）
この簡約は、項 $M$ に対して定義される $M^*$ を用いると非常に強い性質が示せる。
（Takahashi による証明）

#def2
1. $s \Rightarrow s$
2. $x \Rightarrow x$
3. $\lambda x: A. t \Rightarrow \lambda x: A'. t'$ if $A \Rightarrow A'$ and $t \Rightarrow t'$
4. $(x: A) \to t \Rightarrow (x: A') \to t'$ if $A \Rightarrow A'$ and $t \Rightarrow t'$
5. $t_1 t_2 \Rightarrow t_1' t_2'$ if $t_1 \Rightarrow t_1'$ and $t_2 \Rightarrow t_2'$
6. $(\lambda x: A. t_1) t_2 \Rightarrow t_1'[x:= t_2']$ if $t_1 \Rightarrow t_1'$ and $t_2 \Rightarrow t_2'$ and $A \Rightarrow A'$
  - $A \Rightarrow A'$ は帰納法が強くなるようにするため。

このとき、次が成り立つ。

#thm1
1. $t \Rightarrow t$
2. $t \to_\beta t'$ なら $t \Rightarrow t'$
3. $t \Rightarrow t'$ なら $t \to_beta^* t'$
4. $t \Rightarrow t'$, $l \Rightarrow l'$ なら $t[y := l] \Rightarrow t'[y := l']$

証明：
1. $t$ の構造についての帰納法を用いれば、明らか。
2. $t \to_\beta t'$ の導出木に関する帰納法を用いる。
    1. $t_1 t_2 \to_\beta t_1 t_2'$ の場合：帰納法の仮定から、 $t_2 \Rightarrow t_2'$ なので、 #thm1.1 と合わせて $t_1 t_2 \Rightarrow t_1 t_2'$
    2. $t_1 t_2 \to t_1' t_2$ の場合：上と同様
    3. $\lambda x: A. t \to_\beta \lambda x: A'. t$ の場合：上と同様
    4. $\lambda x: A. t \to_\beta \lambda x: A. t'$ の場合：上と同様
    5. $(x: A) \to t \to_\beta (x: A') \to t$ の場合：上と同様
    6. $(x: A) \to t \to_\beta (x: A) \to t'$ の場合：上と同様
    7. $(\lambda x:A. t_1) t_2 \to_\beta t_1[x := t_2]$ の場合：$t_1 \Rightarrow t_1$ と $t_2 \Rightarrow t_2$ より、 #def2.6 から。
3. $t \Rightarrow t'$ の導出木に関する帰納法を用いる。
    1. $s \Rightarrow s$ の場合： $s \to_\beta^* s$ は明らか。
    2. $x \Rightarrow x$ の場合： $x \to_\beta^* x$ は明らか。
    3. $\lambda x: A. t \Rightarrow \lambda x: A'. t'$ の場合：帰納法の仮定から、 $A \to_\beta^* A'$ と $t \to_\beta^* t'$ があるので、 $\lambda x: A. t \to_\beta^* \lambda x:A'. t \to_\beta^* \lambda x:A'. t'$ ができる。
    4. $(x: A) \to t \Rightarrow (x: A') \to t'$ の場合：上と同様。
    5. $t_1 t_2 \Rightarrow t_1' t_2'$ の場合：上と同様。
    6. $(\lambda x: A. t_1) t_2 \Rightarrow t_1'[x:= t_2']$ の場合：帰納法の仮定から $t_1 \to_\beta^* t_1'$ と $t_2 \to_\beta^* t_2'$ と $A \to_\beta^* A'$ があるから、 $(\lambda x: A. t_1) t_2 \to_\beta^* (\lambda x: A'. t_1') t_2' \to_\beta t_1'[x := t_2']$ がわかる。
4. $t \Rightarrow t'$ の導出木に関する帰納法を用いる。
    1. $s \Rightarrow s$ の場合： $s[y := l] \equiv s \Rightarrow s \equiv s[y := l']$ より
    2. $x \Rightarrow x$ の場合：
        - $x = y$ なら、 $x[y := l] \equiv l \Rightarrow l' \equiv x[y := l]$
        - $x \neq y$ なら、 $x[y := l] \equiv x \Rightarrow x \equiv x[y := l']$
    3. $\lambda x: A. t \Rightarrow \lambda x: A'. t'$ の場合：帰納法の仮定から、 $A[y := l] \Rightarrow A'[y := l']$ と $t[y := l] \Rightarrow t'[y := l']$ が得られていて、さらに、 $A \Rightarrow A'$ かつ $t \Rightarrow t'$ である。
        - $x = y$ なら $(\lambda x: A. t)[x := l] \equiv \lambda x:(A[y := l]). t \Rightarrow \lambda x: (A'[y := l']). t' \equiv (\lambda x: A'. t')[y := l']$
        - $x \neq y$ なら、上の議論が $t, t'$ の部分に $[y := l], [y := l']$ が付いただけ。
    4. $(x: A) \to t \Rightarrow (x: A' \to t')$ の場合：上と同様。
    5. $t_1 t_2 \Rightarrow t_1' t_2'$ の場合：帰納法の仮定は $t_1[y := l] \Rightarrow t_1'[y := l']$ と $t_2[y := l] \Rightarrow t_2'[y := l']$ なので、$(t_1 t_2)[y := l]$ を見ればよい。
    6. $(\lambda x: A. t_1) t_2 \Rightarrow t_1'[x:= t_2']$ の場合：帰納法の仮定は、 $t_1[y := l] \Rightarrow t_1'[y := l']$ と $t_2[y := l] \Rightarrow t_2'[y := l']$ と $A[y := l] \Rightarrow A'[y := l']$ である。
      - $x = y$ なら、 $((\lambda x: A. t_1) t_2)[y :=  l] \equiv (\lambda x: A[y := l].t_1) (t_2[y := l]) \Rightarrow t_1'[x := (t_2'[y := l'])] \equiv t_1'[x := t_2'][y := l']$
      - $x \neq y$ なら $((\lambda x: A. t_1) t_2)[y := l] \equiv (\lambda x: A[y := l]. t_1[y := l]) t_2 \Rightarrow (t_1'[y := l'])[x := t_2'[y := l']] \equiv t_1'[x := t_2'][y := l']$ **ラムダ抽象への代入が行える条件から、 $l$はFVに$x$を持ってはいけない。なので、代入の順序を入れ替える補題が使える。**

代入に関する補題として次を用いた。
#lem1
1. $t_1[x := t_2[x := l]] \equiv t_1[x := t_2][x := l]$
2. $x \neq y$ で $x \notin \text{FV}(l)$ なら $t_1[y := l][x := t_2[y := l]] \equiv t_1[x := t_2][y := l]$

証明：
1. $t_1$ に関する帰納法を用いればいい。
    1. $t_1 = s$ なら関係ない
    2. $t_1 = x'$ なら
        - $x = x'$ のとき $x'[x := t_2[x := l]] \equiv t_2[x := l] \equiv x'[x := t_2][x := l]$
        - そうじゃないときは、両辺は $x'$ のまま
    3. $\lambda x':A. t$ なら、
        - $x = x'$ なら $(\lambda x':A. t)[x := t_2[x := l]] \equiv \lambda x': (A[x := t_2[x := l]]). t \equiv \lambda x': (A [x := t_2][x := l]). t \equiv (\lambda x: A. t)[x := t_2][x := l]$
    4. $(x':A) \to t$ なら、上と同様。
    5. $t_1 t_2$ なら、これはそのまま計算した結果が（帰納法の仮定と合わせて）出てくる。
2. $t_1$ に関する帰納法を用いればいい。
    1. $t_1 = s$ なら関係ない
    2. $t_1 = x'$ なら
        - $x' = y$ のときは、 $x \neq y$ より $x \neq x'$ に注意して $x'[y := l][x := t_2[y := l]] \equiv l[x := t_2[y := l]]$
        - $x' \neq y$ のときも同様にして計算する。
    3. 残りは消化試合。

次に、 $M^*$ を次のように定義する。

#def3
1. $s^* = s$
2. $x^* = x$
3. $(\lambda x:A. t)^* = \lambda x: A^*. t^*$
4. $((x: A) \to t)^* = (x: A^*) \to t^*$
5. $(t_1 t_2)^* = t_1^* t_2^*$ if $t_1 \neq \lambda x: A. t$
6. $((\lambda x: A. t) t_2)^* = t^*[x := t_2^*]$

このとき、次が成り立つ。
#lem2
1. $M \Rightarrow N$ なら $N \Rightarrow M^*$

証明：
1. $M$ の構造に関する帰納法を用いる。
    1. $s$ のの場合： $M \Rightarrow N$ なら $N = M = M^*$ である。
    2. $x$ の場合：上と同様
    3. $\lambda x:A. t$ の場合： $N = \lambda x: A'. t'$ のみが考えられる。帰納法の仮定から $A \Rightarrow A' \Rightarrow A^*$, $t \Rightarrow t' \Rightarrow t^*$ が得られている。なので、 $\lambda x: A'. t' \Rightarrow \lambda x: A^*. t^*$
    4. $(x: A) \to t$ の場合は上と同様。
    5. $t_1 t_2$ の場合：
        - $t_1$ が $\lambda$ の形をしていない場合を考える。
            このとき、 $t_1 t_2 \Rightarrow N$ は $t_1 \Rightarrow t_1'$, $t_2 \Rightarrow t_2'$ によって $N = t_1' t_2'$ と書ける。
            帰納法の仮定から、 $t_i' \Rightarrow t_i^:*$ なので、 $t_1 t_2 \Rightarrow t_1' t_2' \Rightarrow t_1^* t_2^*$ よりよい。
        - $t_1 = \lambda x:A. t$ の場合。
            もし規則 5. を用いて導出されたなら、 $\lambda x:A.t \Rightarrow t_1'$ と $t_2 \Rightarrow t_2'$ を用いて
            $M = (\lambda x:A. t) t_2 \Rightarrow t_1' t_2' = N$ となっている。
            ここで、この $t_1'$ は必ず $\lambda x: A'. t'$ の形をしていて、 $A \Rightarrow A', t_1 \Rightarrow t_1'$ であることが（定義を調べると）わかる。
            また、帰納法の仮定から、 $A \rightarrow A' \Rightarrow A^*$, $t \Rightarrow t' \Rightarrow t^*$ が得られている。
            $N = t_1' t_2' = (\lambda x: A'. t') t_2' \Rightarrow $ 

よって、 $\Rightarrow$ の合流性は示せた。
