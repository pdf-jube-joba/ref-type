# Lexing and common syntax

## Whitespace and nested comments

Whitespace separates tokens, and nested comments are excluded from terms.

```toml case
id = "comments"
scope = "module"
expect = "accept"
```

```ref
/* outer /* inner */ outer */
\definition identity
  [P: \Prop]
  [p: P]
  : P
  := /* comment containing { [ ; */ p;
```

## Comment terminator without an opener

A terminator appears where no comment has been opened.

```toml case
id = "unmatched-comment-end"
scope = "module"
expect = "reject"
```

```ref
*/
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

## Parenthesized grouping

Parentheses group expressions, and a proof passed to the identity function proves the resulting proposition.

```toml case
id = "grouping"
scope = "module"
expect = "accept"
parameters = '''P: \Prop, p: P'''
```

```ref
\definition identity[Q: \Prop][q: Q]: Q := q;
\definition applied: P := ((identity P) p);
```

## Unclosed parentheses

The expression's parentheses are unclosed, so syntax checking rejects it.

```toml case
id = "unclosed-parenthesis"
scope = "module"
expect = "reject"
```

```ref
\definition P: \Prop := (\forall (P: \Prop) -> P -> P;
```

## Definition bodies and terminators

A definition with a body is syntactically valid, but omitting the body or terminating delimiter makes it invalid.

```toml scenario
id = "definition-boundaries"
scope = "module"
```

### Body and delimiter present

All required definition elements are present.

```toml step
id = "complete"
expect = "accept"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

### Missing body

No expression follows the assignment symbol.

```toml step
id = "missing-body"
expect = "reject"
```

```ref
\definition P: \Prop := ;
```

### Missing delimiter

The definition has no terminator.

```toml step
id = "missing-semicolon"
expect = "reject"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P
```
