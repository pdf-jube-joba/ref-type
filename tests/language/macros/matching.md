# macros / matching

## duplicate capture

macro の capture 名が重複しているため、拒否される。

```toml case
id = "reject-macros.duplicate_capture"
scope = "module"
expect = "reject"
name = "DuplicateCapture"
```

```ref
\macro invalid($value, $value) := $value;
```

## math extra expression

math macro の一致後に余分な式が残るため、拒否される。

```toml case
id = "reject-macros.math_extra_expression"
scope = "module"
expect = "reject"
name = "MathExtra"
parameters = '''A: \Set(0), x: A, y: A'''
```

```ref
\definition first: A -> A -> A :=
    \fun (left: A) => \fun (right: A) => left;
\math-macro plus($left, \+, $right) := first $left $right;

\definition invalid: A := \(x + y x \);
```

## math operator chain

演算子列全体に一致する math macro が存在しないため、拒否される。

```toml case
id = "reject-macros.math_operator_chain"
scope = "module"
expect = "reject"
name = "MathChain"
parameters = '''A: \Set(0), x: A, y: A'''
```

```ref
\definition first: A -> A -> A :=
    \fun (left: A) => \fun (right: A) => left;
\math-macro plus($left, \+, $right) := first $left $right;

\definition invalid: A := \(x + y + x \);
```

## named literal mismatch

macro 呼び出しの literal が宣言された template と一致しないため、拒否される。

```toml case
id = "reject-macros.named_literal_mismatch"
scope = "module"
expect = "reject"
name = "LiteralMismatch"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro tagged($term, "expected") := $term;

\definition invalid: A := tagged!{value "different"};
```

## non tail recursion depth

非末尾再帰の macro 展開が有限の展開上限を超えるため、拒否される。

```toml case
id = "reject-macros.non_tail_recursion_depth"
scope = "module"
expect = "reject"
name = "Loop"
parameters = '''A: \Set(0), x: A'''
```

```ref
\definition first: A -> A -> A := \fun (a: A) => \fun (b: A) => a;
\macro forever(..r) := first x forever!{..r};
\definition result: A := forever!{};
```

## reserved macro token

macro が構文の予約 token を独自の token として使うため、拒否される。

```toml case
id = "reject-macros.reserved_macro_token"
scope = "module"
expect = "reject"
name = "ReservedMacroToken"
```

```ref
\math-macro invalid($left, \:, $right) := $left;
```

## rest must be last

rest capture の後にさらに capture を置いているため、拒否される。

```toml case
id = "reject-macros.rest_must_be_last"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r, $x) := $x;
```

## self recursion depth

自分自身を展開し続ける macro が有限の展開上限を超えるため、拒否される。

```toml case
id = "reject-macros.self_recursion_depth"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro forever(..r) := forever!{..r};
\definition result: A := forever!{};
```

## token capture requires token

token capture に通常の項として解釈する value を渡しているため、拒否される。

```toml case
id = "reject-macros.token_capture_requires_token"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro select(tk) := value;
\definition result: A := select!{value};
```

## token match no branch

入力 token に一致する token match の分岐がないため、拒否される。

```toml case
id = "reject-macros.token_match_no_branch"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro select(tk) := \tmatch tk { | \+ => value };
\definition result: A := select!{"+"};
```

## local expansion

局所文脈の式を macro の capture に渡せるため、受理される。

```toml case
id = "accept-macros.local_expansion"
scope = "module"
expect = "accept"
name = "LocalMacros"
parameters = '''A: \Set(0), x: A, y: A'''
```

```ref
\definition first: A -> A -> A :=
    \fun (left: A) => \fun (right: A) => left;

\math-macro plus($left, \+, $right) := first $left $right;
\math-macro meet($left, \/\, $right) := first $left $right;
\macro via_math($left, $right) := \($left + $right \);
\macro tagged($term, "keep") := $term;

\definition simple: A := \(x + y \);
\definition nested: A := \((x + y) + (x /\ y) \);
\definition composed: A := via_math!{x y};
\definition quoted: A := tagged!{y "keep"};
```

## variadic token match

可変長 capture と token match を組み合わせて展開できるため、受理される。

```toml case
id = "accept-macros.variadic_token_match"
scope = "module"
expect = "accept"
name = "Variadic"
parameters = '''A: \Set(0), x: A, y: A'''
```

```ref
\definition tk: A := y;
\definition first: A -> A -> A := \fun (a: A) => \fun (b: A) => a;
\definition second: A -> A -> A := \fun (a: A) => \fun (b: A) => b;
\math-macro plus($a, \+, $b) := first $a $b;
\macro choose($a, tk, $b) :=
    \tmatch tk {
        | \+ => first
        | "+" => second
        | _ => first
    } $a $b;
\macro identity($x) := $x;
\macro explicit_expression(tk) := identity!{{ tk }};
\macro token_scope(tk) := choose!{x tk y};
\macro forward($a,tk,..r) := choose!{$a tk ..r};
\macro math_forward($a, tk, ..r) := \($a tk ..r \);
\macro math_rest(..r) := \(..r \);
\macro last(..r) := \tmatch r {
    | () => x
    | ($t) => $t
    | ($t,..rest) => last!{..rest}
};
\macro repeated(..r) := last!{..r ..r};
\macro fold(..r) := \tmatch r {
    | () => x
    | ($t,..tail) => second $t fold!{..tail}
};
\macro relay(..r) := last!{..r};
\macro grouped((..r), "end") := relay!{..r};
\macro preserve(..r) := grouped!{..r};
\macro inspect(..r) := \tmatch r {
    | ((tk, $a, ..tail), "end") => \tmatch tk {
        | "keep" => $a
        | _ => last!{..tail}
    }
    | _ => x
};
\macro no_match(tk) := \tmatch tk {};
\macro lazy(tk) := \tmatch tk {
    | "stop" => x
    | _ => no_match!{tk}
};
\macro again(tk, ..r) := \tmatch tk {
    | "stop" => last!{..r}
    | _ => again!{"stop" ..r}
};

\definition explicit_atom: explicit_expression!{+} = y := \refl(y);
\definition bare_token: token_scope!{+} = x := \refl(x);
\definition repeat: repeated!{x y} = y := \refl(y);
\definition symbol: forward!{x + y} = x := \refl(x);
\definition quoted: forward!{x "+" y} = y := \refl(y);
\definition fallback: choose!{x - y} = x := \refl(x);
\definition math: math_forward!{x + y} = x := \refl(x);
\definition nested_math: math_rest!{(x + y) + y} = x := \refl(x);
\definition folded: fold!{y y y y} = x := \refl(x);
\definition empty: relay!{} = x := \refl(x);
\definition single: relay!{y} = y := \refl(y);
\definition multiple: relay!{x y x y} = y := \refl(y);
\definition group: preserve!{(x y) "end"} = y := \refl(y);
\definition empty_group: preserve!{() "end"} = x := \refl(x);
\definition nested_capture: inspect!{("keep" y x) "end"} = y := \refl(y);
\definition nested_rest: inspect!{("last" x x y) "end"} = y := \refl(y);
\definition unevaluated: lazy!{"stop"} = x := \refl(x);
\definition token_recursion: again!{"start" x y} = y := \refl(y);
```


## math macro の優先順位

同じ pattern に合う macro が二つあるとき、先に定義された A を返す macro が選ばれる。

```toml case
id = "earlier_math_macro_wins_when_patterns_are_equally_applicable"
scope = "module"
expect = "accept"
name = "Priority"
parameters = '''A: \Set(0), B: \Set(0), a: A, b: B'''
```

```ref
\definition keep_a: A -> A -> A := \fun (left: A) => \fun (right: A) => left;
\definition keep_b: A -> A -> B := \fun (left: A) => \fun (right: A) => b;
\math-macro earlier($left, \+, $right) := keep_a $left $right;
\math-macro later($left, \+, $right) := keep_b $left $right;
\definition selected: A := \(a + a \);
```

## macro の裸の推論穴

macro の式引数として裸の穴を渡し、後続の引数から型を推論できる。

```toml case
id = "bare_underscore_is_a_macro_expression_argument"
scope = "module"
expect = "accept"
name = "Underscore"
parameters = '''A: \Set(0), f: A, y: A'''
```

```ref
\definition first: \forall (T: \Set(0)) -> T -> T -> T :=
  \fun (T: \Set(0)) => \fun (a: T) => \fun (b: T) => a;
\macro two($type, $value) := first $type $value y;
\definition bare_hole_with_next_argument: A := two!{_ f};
```

## capture の分類 / 5

宣言していない sequence capture を展開しているため拒否される。

```toml case
id = "capture-judgement-4"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := last!{..missing};
```

## capture の分類 / 6

expression capture を sequence として展開しているため拒否される。

```toml case
id = "capture-judgement-5"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad($x) := last!{..x};
```

## capture の分類 / 7

token capture を expression として参照しているため拒否される。

```toml case
id = "capture-judgement-6"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(tk) := $tk;
```

## capture の分類 / 8

sequence capture を expression として参照しているため拒否される。

```toml case
id = "capture-judgement-7"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := $r;
```

## capture の分類 / 9

expression capture を token match の対象にしているため拒否される。

```toml case
id = "capture-judgement-8"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad($x) := \tmatch x {};
```

## capture の分類 / 11

token capture に sequence の match pattern を書いているため拒否される。

```toml case
id = "capture-judgement-10"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(tk) := \tmatch tk { | () => value };
```

## capture の分類 / 12

sequence capture に token の match pattern を書いているため拒否される。

```toml case
id = "capture-judgement-11"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := \tmatch r { | \+ => value };
```

## capture の分類 / 16

token match の分岐の外で分岐内の capture を参照しているため拒否される。

```toml case
id = "capture-judgement-15"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := \tmatch r { | ($x) => $x } $x;
```

## capture の分類 / 18

math macro の pattern に named macro 用の token capture を書いているため拒否される。

```toml case
id = "capture-judgement-17"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\math-macro bad(tk, \+) := value;
```

## operator のない math macro

math macro の pattern に operator token がないため拒否される。

```toml case
id = "macro-template-4"
scope = "module"
expect = "reject"
name = "NoToken"
```

```ref
\math-macro bad($value) := $value;
```

## 未宣言の expression capture

template が宣言されていない capture を使っているため拒否される。

```toml case
id = "macro-template-5"
scope = "module"
expect = "reject"
name = "UnknownCapture"
```

```ref
\macro bad($value) := $other;
```

## token match / string-for-symbol

文字列 token は記号 token の pattern に一致しないため拒否される。

```toml case
id = "token-match-string-for-symbol"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro m(tk) := \tmatch tk { | \+ => value }; \definition result: A := m!{"+"};
```

## token match / symbol-for-string

記号 token は文字列 token の pattern に一致しないため拒否される。

```toml case
id = "token-match-symbol-for-string"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro m(tk) := \tmatch tk { | "+" => value }; \definition result: A := m!{+};
```

## token match / group-for-token

括弧で囲った sequence を単独の token capture に渡しているため拒否される。

```toml case
id = "token-match-group-for-token"
scope = "module"
expect = "reject"
name = "Invalid"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro m(tk) := value; \definition result: A := m!{(+)};
```
