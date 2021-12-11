# motivation
Type `2` as `2N` without existence of oracle `SMT : predicate -> Bool`.
Instead , user must solve a inhabitants problem.

# definition of system
## definition of term
```
<term> = Var <var> | Sort Type | Sort Prop
  | Fun <var> <term> <term>
  | For <var> <term> <term>
  | App <term> <term>
  | Ref <term> <term>
  | Prf <term>
```
context are defined as usual

## definition of judgement and type system
there is three form of judgement

```
|- G ... well-formedness of context
G |- t : T ... typing rule
G |= T ... inhabitants of type
```

let S = {Type , Prop} , A = {(Prop , Type)} , R = {(Prop , Prop) , (Prop , Type) , (Type , Prop) , (Type , Type)}

derivation rule contains CoC rule

- empty context
  ```
  ---
  |-
  ```
- well-formed context
  ```
  G |- A : S
  ---
  |- G , x : A
  ```
  where `s` is in S and `x` is not in `G`
- axiom
  ```
  ---
  |- s1 : s2
  ```
  where `(s1 , s2)` is in A
- variable
  ```
  |- G , x : A
  ---
  G , x : A |- x : A
  ```
- weakning
  ```
  G |- t : T
  ---
  G , x : A |- t : T
  ```
- for formation
  ```
  G |- A : s1
  G , x : A |- B : s2
  ---
  G |- For x A B : s2
  ```
  where `(s1 , s2)` is in R
- fun introduction
  ```
  G |- For x A B : s
  G , x : A |- t : B
  ---
  G |- Fun x A t : For x A B
  ```
  where `s` is in S
- app elimination
  ```
  G |- t1 : For x A B
  G |- t2 : A
  ---
  G |- App t1 t2 : B{x <- t2}
  ```
- conversion rule
  ```
  G |- t : A
  G |- B : s
  ---
  G |- t : B
  ```
  where `s` is in S and two term `A` , `B` are beta equivalence

in addition to

- Ref form
  ```
  G |- A : Type
  G |- P : For x A Prop
  ---
  G |- Ref A P : Type
  ```
- Ref intro
  ```
  G |- Ref A P : Type
  G |- t : A
  G |= App P t
  ---
  G |- t : Ref A P
  ```
- Ref elim
  ```
  G |- t : Ref A P
  ---
  G |- t : A
  ```
- implicit proof
  ```
  G |- P : Prop
  G |- t : P
  ---
  G |= P
  ```
- explicit proof
  ```
  G |= P
  ---
  G |- Prf P : P
  ```
- refinement inversion
  ```
  G |- t : Ref A P
  ---
  G |= App P t
  ```

# TODO list
- beta reduction and conversion
  - [ ] Church-Rosser
  - [ ] Confluence
- as type system
  - [ ] `G |- t : T` then `G |- T : s` for some `s` in S
  - [ ] Weakening
  - [ ] Strengthening
  - [ ] Subject reduction
  - [ ] Strong normalization
  - [ ] type check decidability(?)
- as logic system
  - [ ] for any context `G` and term `t` , `T` of CoC , `G |- t : T` iff `G |-_{CoC} t : T` ?
  - [ ] consistency