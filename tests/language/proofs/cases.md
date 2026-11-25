# Explicit proof terms

## Subset introduction using membership proofs

An assumed membership proof can introduce an ambient-set element as a subset element.

```toml case
id = "subset-introduction-with-membership-proof"
scope = "module"
expect = "accept"
parameters = '''A: \Set,
  a: \Pow (A),
  x: A,
  p: \In[A] (a) (x),'''
```

```ref
\definition h: \Cast[A] (a) := \into[A](x, a) \by { p };
```

## Explicit proof terms

Explicit proof terms corresponding to proposition constructions can be written.

```toml case
id = "explicit-proof-terms"
scope = "module"
expect = "accept"
name = "ExplicitProofTerms"
parameters = '''A: \Set,
  S: \Pow (A),
  x: A,
  refined: \Cast[A] (S),'''
```

```ref
\definition inhabited: \exists A := \exact(x, A);
\definition reflexive: x = x := \refl(x);
\definition membership: \In[A] (S) (refined) := \bysub(A, S, refined);
```

