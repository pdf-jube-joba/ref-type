import RefType.Syntax

namespace RefType.Original

abbrev OSort := RefType.USort

/-! The unstratified presentation from `doc/book/src/system.md`.  Unlike the
proof-oriented syntax in `RefType`, every object belongs to one expression
grammar and variables carry the sort annotation written as `x^s` in the
document. -/

inductive Expr where
  | sort : OSort → Expr
  | var : OSort → Nat → Expr
  | prod : OSort → Expr → Expr → Expr
  | lam : OSort → Expr → Expr → Expr
  | app : Expr → Expr → Expr
  | prove : Expr → Expr
  | power : Expr → Expr
  | subset : OSort → Expr → Expr → Expr
  | typeLift : Expr → Expr → Expr
  | pred : Expr → Expr → Expr → Expr
  | equal : Expr → Expr → Expr
  | exists_ : Expr → Expr
  | take : Expr → Expr → Expr → Expr
  deriving DecidableEq, Repr

def falseProp : Expr :=
  .prod .propKind (.sort .prop) (.var .propKind 0)

def Expr.liftFrom (cutoff : Nat) : Expr → Expr
  | .sort s => .sort s
  | .var s k => if cutoff ≤ k then .var s (k + 1) else .var s k
  | .prod s A B => .prod s (A.liftFrom cutoff) (B.liftFrom (cutoff + 1))
  | .lam s A body => .lam s (A.liftFrom cutoff) (body.liftFrom (cutoff + 1))
  | .app f a => .app (f.liftFrom cutoff) (a.liftFrom cutoff)
  | .prove P => .prove (P.liftFrom cutoff)
  | .power A => .power (A.liftFrom cutoff)
  | .subset s A P => .subset s (A.liftFrom cutoff) (P.liftFrom (cutoff + 1))
  | .typeLift A B => .typeLift (A.liftFrom cutoff) (B.liftFrom cutoff)
  | .pred A B t => .pred (A.liftFrom cutoff) (B.liftFrom cutoff) (t.liftFrom cutoff)
  | .equal a b => .equal (a.liftFrom cutoff) (b.liftFrom cutoff)
  | .exists_ A => .exists_ (A.liftFrom cutoff)
  | .take X T f => .take (X.liftFrom cutoff) (T.liftFrom cutoff) (f.liftFrom cutoff)

def Expr.subst (idx : Nat) (replacement : Expr) : Expr → Expr
  | .sort s => .sort s
  | .var s k =>
      if k = idx then replacement
      else if idx < k then .var s (k - 1)
      else .var s k
  | .prod s A B =>
      .prod s (Expr.subst idx replacement A)
        (Expr.subst (idx + 1) (replacement.liftFrom 0) B)
  | .lam s A body =>
      .lam s (Expr.subst idx replacement A)
        (Expr.subst (idx + 1) (replacement.liftFrom 0) body)
  | .app f a => .app (Expr.subst idx replacement f) (Expr.subst idx replacement a)
  | .prove P => .prove (Expr.subst idx replacement P)
  | .power A => .power (Expr.subst idx replacement A)
  | .subset s A P =>
      .subset s (Expr.subst idx replacement A)
        (Expr.subst (idx + 1) (replacement.liftFrom 0) P)
  | .typeLift A B =>
      .typeLift (Expr.subst idx replacement A) (Expr.subst idx replacement B)
  | .pred A B t =>
      .pred (Expr.subst idx replacement A) (Expr.subst idx replacement B)
        (Expr.subst idx replacement t)
  | .equal a b => .equal (Expr.subst idx replacement a) (Expr.subst idx replacement b)
  | .exists_ A => .exists_ (Expr.subst idx replacement A)
  | .take X T f =>
      .take (Expr.subst idx replacement X) (Expr.subst idx replacement T)
        (Expr.subst idx replacement f)

notation:70 E "[" u "]" => Expr.subst 0 u E

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
  | predSubset {s A B P t} :
      Reduces (.pred A (.subset s B P) t) (.app (.lam s B P) t)
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

structure Decl where
  sort : OSort
  ty : Expr
  deriving DecidableEq, Repr

abbrev Context := List Decl

inductive Lookup : Context → Nat → Expr → OSort → Prop where
  | here {Γ A s} :
      Lookup ({ sort := s, ty := A } :: Γ) 0 (A.liftFrom 0) s
  | there {Γ n A s A' s'} :
      Lookup Γ n A s →
      Lookup ({ sort := s', ty := A' } :: Γ) (n + 1) (A.liftFrom 0) s

inductive Sequent where
  | wf
  | hasSort : Expr → OSort → Sequent
  | hasType : Expr → Expr → OSort → Sequent
  | provable : Expr → Sequent
  deriving Repr

inductive Derives : Context → Sequent → Prop where
  | wfEmpty :
      Derives [] .wf
  | wfExtend {Γ A s} :
      Derives Γ .wf →
      Derives Γ (.hasSort A s) →
      Derives ({ sort := s, ty := A } :: Γ) .wf
  | sortAxiom {s t} :
      RefType.USort.axiomTarget? s = some t →
      Derives [] (.hasSort (.sort s) t)
  | sortWeak {Γ d A s} :
      Derives Γ (.hasSort A s) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.hasSort (A.liftFrom 0) s)
  | typeWeak {Γ d e A s} :
      Derives Γ (.hasType e A s) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.hasType (e.liftFrom 0) (A.liftFrom 0) s)
  | propWeak {Γ d P} :
      Derives Γ (.provable P) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.provable (P.liftFrom 0))
  | var {Γ i A s} :
      Derives Γ .wf →
      Lookup Γ i A s →
      Derives Γ (.hasType (.var s i) A s)
  | typeElem {Γ A s t} :
      Derives Γ (.hasSort A s) →
      Derives Γ (.hasSort (.sort s) t) →
      Derives Γ (.hasType A (.sort s) t)
  | prodForm {Γ binderSort A B bodySort resultSort} :
      Derives Γ (.hasSort A binderSort) →
      Derives ({ sort := binderSort, ty := A } :: Γ) (.hasSort B bodySort) →
      RefType.USort.prodResult? binderSort bodySort = some resultSort →
      Derives Γ (.hasSort (.prod binderSort A B) resultSort)
  | lamIntro {Γ binderSort A body B bodySort resultSort} :
      Derives Γ (.hasSort (.prod binderSort A B) resultSort) →
      Derives ({ sort := binderSort, ty := A } :: Γ) (.hasType body B bodySort) →
      Derives Γ (.hasType (.lam binderSort A body) (.prod binderSort A B) resultSort)
  | appElim {Γ f a binderSort A B bodySort resultSort} :
      Derives Γ (.hasType f (.prod binderSort A B) resultSort) →
      Derives Γ (.hasType a A binderSort) →
      Derives Γ (.hasSort (B[a]) bodySort) →
      Derives Γ (.hasType (.app f a) (B[a]) bodySort)
  | typeConv {Γ e A B s} :
      Derives Γ (.hasType e A s) →
      Derives Γ (.hasSort B s) →
      A ≃β B →
      Derives Γ (.hasType e B s)
  | provableIntro {Γ p P} :
      Derives Γ (.hasType p P .prop) →
      Derives Γ (.provable P)
  | proveTerm {Γ P} :
      Derives Γ (.provable P) →
      Derives Γ (.hasType (.prove P) P .prop)
  | powerForm {Γ A i} :
      Derives Γ (.hasSort A (.set i)) →
      Derives Γ (.hasSort (.power A) (.set i))
  | subsetForm {Γ A P i} :
      Derives Γ (.hasSort A (.set i)) →
      Derives ({ sort := .set i, ty := A } :: Γ) (.hasSort P .prop) →
      Derives Γ (.hasType (.subset (.set i) A P) (.power A) (.set i))
  | predForm {Γ A B t i} :
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.hasType t A (.set i)) →
      Derives Γ (.hasSort (.pred A B t) .prop)
  | typeLiftForm {Γ A B i} :
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.hasSort (.typeLift A B) (.set i))
  | typeLiftIntro {Γ t A B i} :
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.hasType t A (.set i)) →
      Derives Γ (.provable (.pred A B t)) →
      Derives Γ (.hasType t (.typeLift A B) (.set i))
  | typeLiftWeak {Γ t A B i} :
      Derives Γ (.hasType t (.typeLift A B) (.set i)) →
      Derives Γ (.hasType t A (.set i))
  | subsetProp {Γ t A B i} :
      Derives Γ (.hasType t (.typeLift A B) (.set i)) →
      Derives Γ (.provable (.pred A B t))
  | equalForm {Γ a b A i} :
      Derives Γ (.hasType a A (.set i)) →
      Derives Γ (.hasType b A (.set i)) →
      Derives Γ (.hasSort (.equal a b) .prop)
  | equalRefl {Γ a A i} :
      Derives Γ (.hasType a A (.set i)) →
      Derives Γ (.provable (.equal a a))
  | equalElim {Γ a b A P i} :
      Derives Γ (.hasType a A (.set i)) →
      Derives Γ (.hasType b A (.set i)) →
      Derives Γ (.provable (.equal a b)) →
      Derives ({ sort := .set i, ty := A } :: Γ) (.hasSort P .prop) →
      Derives Γ (.provable (.app (.lam (.set i) A P) a)) →
      Derives Γ (.provable (.app (.lam (.set i) A P) b))
  | existsForm {Γ A i} :
      Derives Γ (.hasSort A (.set i)) →
      Derives Γ (.hasSort (.exists_ A) .prop)
  | existsIntro {Γ e A i} :
      Derives Γ (.hasType e A (.set i)) →
      Derives Γ (.provable (.exists_ A))
  | takeSet {Γ X T f i} :
      Derives Γ (.hasSort X (.set i)) →
      Derives Γ (.hasSort T (.set i)) →
      Derives Γ (.hasType f (.prod (.set i) X (T.liftFrom 0)) (.set i)) →
      Derives Γ (.provable (.exists_ X)) →
      Derives Γ (.provable
        (.prod (.set i) X
          (.prod (.set i) (X.liftFrom 0)
            (.equal
              (.app (f.liftFrom 0 |>.liftFrom 0) (.var (.set i) 1))
              (.app (f.liftFrom 0 |>.liftFrom 0) (.var (.set i) 0)))))) →
      Derives Γ (.hasType (.take X T f) T (.set i))
  | takeProp {Γ X T f i} :
      Derives Γ (.hasSort X (.set i)) →
      Derives Γ (.hasSort T .prop) →
      Derives Γ (.hasType f (.prod (.set i) X (T.liftFrom 0)) .prop) →
      Derives Γ (.provable (.exists_ X)) →
      Derives Γ (.hasType (.take X T f) T .prop)
  | takeEq {Γ f t T X i} :
      Derives Γ (.hasType (.take X T f) T (.set i)) →
      Derives Γ (.hasType t X (.set i)) →
      Derives Γ (.provable (.equal (.take X T f) (.app f t)))

def WF (Γ : Context) : Prop := Derives Γ .wf
def HasSort (Γ : Context) (A : Expr) (s : OSort) : Prop := Derives Γ (.hasSort A s)
def HasType (Γ : Context) (e A : Expr) (s : OSort) : Prop := Derives Γ (.hasType e A s)
def Provable (Γ : Context) (P : Expr) : Prop := Derives Γ (.provable P)

def PTSTyping (Γ : Context) (e A : Expr) : Prop :=
  (∃ s, A = .sort s ∧ HasSort Γ e s) ∨ ∃ s, HasType Γ e A s

notation:max "|-₀ " Γ => WF Γ
notation:55 Γ " |-₀ " A " :: " s => HasSort Γ A s
notation:55 Γ " |-₀ " e " : " A " :: " s => HasType Γ e A s
notation:55 Γ " |=₀ " P => Provable Γ P

end RefType.Original
