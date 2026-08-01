import RefType.Original.Subst

namespace RefType.Original

inductive Reduces : Expr → Expr → Prop where
  | beta {s A body arg} :
      Reduces (.app (.lam s A body) arg) (body[arg])
  | prodDom {s A A' B} :
      Reduces A A' → Reduces (.prod s A B) (.prod s A' B)
  | prodCodom {s A B B'} :
      Reduces B B' → Reduces (.prod s A B) (.prod s A B')
  | lamTy {s A A' body} :
      Reduces A A' → Reduces (.lam s A body) (.lam s A' body)
  | lamBody {s A body body'} :
      Reduces body body' → Reduces (.lam s A body) (.lam s A body')
  | appFn {f f' a} :
      Reduces f f' → Reduces (.app f a) (.app f' a)
  | appArg {f a a'} :
      Reduces a a' → Reduces (.app f a) (.app f a')
  | prove {P P'} :
      Reduces P P' → Reduces (.prove P) (.prove P')
  | power {A A'} :
      Reduces A A' → Reduces (.power A) (.power A')
  | subsetBase {s A A' P} :
      Reduces A A' → Reduces (.subset s A P) (.subset s A' P)
  | subsetPred {s A P P'} :
      Reduces P P' → Reduces (.subset s A P) (.subset s A P')
  | predSubset {s A P t} :
      Reduces (.pred A (.subset s A P) t) (P[t])
  | typeLiftLeft {A A' B} :
      Reduces A A' → Reduces (.typeLift A B) (.typeLift A' B)
  | typeLiftRight {A B B'} :
      Reduces B B' → Reduces (.typeLift A B) (.typeLift A B')
  | predLeft {A A' B t} :
      Reduces A A' → Reduces (.pred A B t) (.pred A' B t)
  | predMid {A B B' t} :
      Reduces B B' → Reduces (.pred A B t) (.pred A B' t)
  | predRight {A B t t'} :
      Reduces t t' → Reduces (.pred A B t) (.pred A B t')
  | equalLeft {a a' b} :
      Reduces a a' → Reduces (.equal a b) (.equal a' b)
  | equalRight {a b b'} :
      Reduces b b' → Reduces (.equal a b) (.equal a b')
  | exists_ {A A'} :
      Reduces A A' → Reduces (.exists_ A) (.exists_ A')
  | takeDomain {X X' T f} :
      Reduces X X' → Reduces (.take X T f) (.take X' T f)
  | takeCodomain {X T T' f} :
      Reduces T T' → Reduces (.take X T f) (.take X T' f)
  | takeFunction {X T f f'} :
      Reduces f f' → Reduces (.take X T f) (.take X T f')

inductive BetaEq : Expr → Expr → Prop where
  | refl (e) : BetaEq e e
  | step : Reduces e e' → BetaEq e e'
  | symm : BetaEq e e' → BetaEq e' e
  | trans : BetaEq e e' → BetaEq e' e'' → BetaEq e e''

infix:50 " ⇒β " => Reduces
infix:50 " ≃β " => BetaEq

end RefType.Original
