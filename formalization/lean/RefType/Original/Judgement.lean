import RefType.Original.Reduction

namespace RefType.Original

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
      Derives Γ (.hasType (.var i) A s)
  | sortAsType {Γ A s t} :
      Derives Γ (.hasSort A s) →
      Derives Γ (.hasSort (.sort s) t) →
      Derives Γ (.hasType A (.sort s) t)
  | typeAsSort {Γ A s t} :
      Derives Γ (.hasType A (.sort s) t) →
      Derives Γ (.hasSort A s)
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
      Derives Γ (.hasType t A (.set i)) →
      Derives Γ (.hasType B (.power A) (.set i)) →
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
      Derives Γ (.provable (P[a])) →
      Derives Γ (.provable (P[b]))
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
              (.app (f.liftFrom 0 |>.liftFrom 0) (.var 1))
              (.app (f.liftFrom 0 |>.liftFrom 0) (.var 0)))))) →
      Derives Γ (.hasType (.take X T f) T (.set i))
  | takeProp {Γ X T f i} :
      Derives Γ (.hasSort X (.set i)) →
      Derives Γ (.hasSort T .prop) →
      Derives Γ (.hasType f (.prod (.set i) X (T.liftFrom 0)) .prop) →
      Derives Γ (.provable (.exists_ X)) →
      Derives Γ (.hasType (.take X T f) T .prop)
  | takeEq {Γ f t T X i} :
      Derives Γ (.hasType (.take X T f) T (.set i)) →
      Derives Γ (.hasType f (.prod (.set i) X (T.liftFrom 0)) (.set i)) →
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

theorem falsePropFormed : HasSort [] falseProp .prop := by
  have hProp : HasSort [] (.sort .prop) .propKind := Derives.sortAxiom rfl
  have hctx : WF [{ sort := .propKind, ty := .sort .prop }] :=
    Derives.wfExtend Derives.wfEmpty hProp
  have hvarType :
      HasType [{ sort := .propKind, ty := .sort .prop }]
        (.var 0) (.sort .prop) .propKind := by
    change HasType [{ sort := .propKind, ty := .sort .prop }]
      (.var 0) ((Expr.sort .prop).liftFrom 0) .propKind
    exact Derives.var hctx Lookup.here
  have hbody :
      HasSort [{ sort := .propKind, ty := .sort .prop }] (.var 0) .prop :=
    Derives.typeAsSort hvarType
  exact Derives.prodForm hProp hbody rfl

end RefType.Original
