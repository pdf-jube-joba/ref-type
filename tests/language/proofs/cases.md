# proofs / cases

## admit proof

明示的に admit した証明項を宣言された命題の証明として使えるため、受理される。

```toml case
id = "accept-proofs.admit_proof"
scope = "module"
expect = "accept"
name = "Test"
parameters = '''A: \Set,
  a: \Pow (A),
  x: A,
  p: \In[A] (a) (x),'''
```

```ref
\definition h: \Cast[A] (a) := \into[A](x, a) \by { p };
```

## explicit proof terms

命題の構成に対応する明示的な証明項を記述できるため、受理される。

```toml case
id = "accept-proofs.explicit_proof_terms"
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

