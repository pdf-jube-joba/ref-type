# Macro patterns and token matching

## Duplicate capture

Macro capture names are duplicated.

```toml case
id = "duplicate-capture"
scope = "module"
expect = "reject"
name = "DuplicateCapture"
```

```ref
\macro invalid($value, $value) := $value;
```

## Math extra expression

Extra expressions remain after a math macro match.

```toml case
id = "math-extra-expression"
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

## Math operator chain

No math macro matches the entire operator sequence.

```toml case
id = "math-operator-chain"
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

## Named literal mismatch

A macro call's literal does not match the declared template.

```toml case
id = "named-literal-mismatch"
scope = "module"
expect = "reject"
name = "LiteralMismatch"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro tagged($term, "expected") := $term;

\definition invalid: A := tagged!{value "different"};
```

## Non tail recursion depth

Non-tail-recursive macro expansion exceeds the finite expansion limit.

```toml case
id = "non-tail-recursion-depth"
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

## Reserved macro token

A macro uses a reserved syntax token as its own token.

```toml case
id = "reserved-macro-token"
scope = "module"
expect = "reject"
name = "ReservedMacroToken"
```

```ref
\math-macro invalid($left, \:, $right) := $left;
```

## Rest must be last

Another capture follows a rest capture.

```toml case
id = "rest-must-be-last"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r, $x) := $x;
```

## Self recursion depth

A macro that continually expands itself exceeds the finite expansion limit.

```toml case
id = "self-recursion-depth"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro forever(..r) := forever!{..r};
\definition result: A := forever!{};
```

## Token capture requires token

A value interpreted as an ordinary term is passed to a token capture.

```toml case
id = "token-capture-requires-token"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro select(tk) := value;
\definition result: A := select!{value};
```

## Token match no branch

The input is a quoted token of the right kind, but its text matches none of the branches.

```toml case
id = "token-match-no-branch"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro choose(token) := \tmatch token {
  | "keep" => value
};
\definition result: A := choose!{"drop"};
```

## Local expansion

Expressions in local contexts can be passed to macro captures.

```toml case
id = "local-expansion"
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

## Variadic token match

Variadic captures and token matching can be combined during expansion.

```toml case
id = "variadic-token-match"
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


## Math macro precedence

When two macros match the same pattern, the earlier macro returning A is selected.

```toml case
id = "earlier-math-macro-wins-when-patterns-are-equally-applicable"
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

## Bare inference holes in macros

A bare hole can be passed as a macro expression argument, with its type inferred from later arguments.

```toml case
id = "bare-underscore-is-a-macro-expression-argument"
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

## Undeclared sequence captures

An undeclared sequence capture is expanded.

```toml case
id = "undeclared-rest-capture"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro collect(..values) := value;
\macro bad(..values) := collect!{..missing};
```

## Expression captures cannot be spliced as sequences

An expression capture is expanded as a sequence.

```toml case
id = "expression-capture-used-as-sequence"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro collect(..values) := value;
\macro bad($x) := collect!{..x};
```

## Token captures cannot be used as expressions

A token capture is referenced as an expression.

```toml case
id = "token-capture-used-as-expression"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(tk) := $tk;
```

## Sequence captures cannot be used as expressions

A sequence capture is referenced as an expression.

```toml case
id = "sequence-capture-used-as-expression"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := $r;
```

## Expression captures cannot be token-match subjects

An expression capture is used as a token-match subject.

```toml case
id = "expression-capture-used-as-match-subject"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad($x) := \tmatch x {};
```

## Sequence patterns cannot match token captures

A sequence match pattern is written for a token capture.

```toml case
id = "sequence-pattern-for-token-capture"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(tk) := \tmatch tk { | () => value };
```

## Token patterns cannot match sequence captures

A token match pattern is written for a sequence capture.

```toml case
id = "token-pattern-for-sequence-capture"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := \tmatch r { | \+ => value };
```

## Token-match captures remain inside their branch

A capture bound inside a token-match branch is referenced outside the branch.

```toml case
id = "branch-capture-escapes-token-match"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro bad(..r) := \tmatch r { | ($x) => $x } $x;
```

## Math macro patterns reject token captures

A token capture intended for named macros is written in a math macro pattern.

```toml case
id = "math-pattern-rejects-token-captures"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\math-macro bad(tk, \+) := value;
```

## Math macro patterns require a fixed token

A math macro pattern has no operator token.

```toml case
id = "math-pattern-requires-fixed-token"
scope = "module"
expect = "reject"
name = "NoToken"
```

```ref
\math-macro bad($value) := $value;
```

## Undeclared expression captures

A template uses an undeclared capture.

```toml case
id = "undeclared-expression-capture"
scope = "module"
expect = "reject"
name = "UnknownCapture"
```

```ref
\macro bad($value) := $other;
```

## Token match / string-for-symbol

String tokens do not match symbol-token patterns.

```toml case
id = "token-match-string-for-symbol"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro m(tk) := \tmatch tk { | \+ => value }; \definition result: A := m!{"+"};
```

## Token match / symbol-for-string

Symbol tokens do not match string-token patterns.

```toml case
id = "token-match-symbol-for-string"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro m(tk) := \tmatch tk { | "+" => value }; \definition result: A := m!{+};
```

## Token match / group-for-token

A parenthesized sequence is passed to a single token capture.

```toml case
id = "token-match-group-for-token"
scope = "module"
expect = "reject"
parameters = '''A: \Set(0), value: A'''
```

```ref
\macro m(tk) := value;
\definition result: A := m!{(+)};
```
