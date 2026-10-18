# 字句と共通構文

## 空白と入れ子のコメント

空白は区切りとして扱い、入れ子のコメントは項に含めない。

```toml case
id = "comments"
scope = "module"
expect = "accept"
```

```ref
/* 外側 /* 内側 */ 外側 */
\definition identity
  (P: \Prop)
  (p: P)
  : P
  := /* コメントの中の { [ ; */ p;
```

## 対応する開始がないコメントの終端

コメントを開始していない位置で終端が現れる。

```toml case
id = "unmatched-comment-end"
scope = "module"
expect = "reject"
```

```ref
*/
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

## 括弧による grouping

括弧は式を grouping し、恒等関数に渡した証明は結果の命題を証明する。

```toml case
id = "grouping"
scope = "module"
expect = "accept"
parameters = '''P: \Prop, p: P'''
```

```ref
\definition identity(Q: \Prop)(q: Q): Q := q;
\definition applied: P := ((identity P) p);
```

## 閉じていない括弧

式の括弧が閉じていないため、構文の検査で拒否される。

```toml case
id = "unclosed-parenthesis"
scope = "module"
expect = "reject"
```

```ref
\definition P: \Prop := (\forall (P: \Prop) -> P -> P;
```

## definition の本体と終端

本体を持つ definition は構文として成立するが、本体または終端の区切りが欠けていると成立しない。

```toml scenario
id = "definition-boundaries"
scope = "module"
```

### 本体と区切りがある

definition の必要な要素がそろっている。

```toml step
id = "complete"
expect = "accept"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P;
```

### 本体が欠けている

代入記号の後に式がない。

```toml step
id = "missing-body"
expect = "reject"
```

```ref
\definition P: \Prop := ;
```

### 区切りが欠けている

definition の終端がない。

```toml step
id = "missing-semicolon"
expect = "reject"
```

```ref
\definition P: \Prop := \forall (P: \Prop) -> P -> P
```
