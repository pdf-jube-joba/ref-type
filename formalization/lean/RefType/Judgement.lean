import RefType.Reduction

namespace RefType

structure Decl where
  kind : VarKind
  sort : USort
  ty : TyExpr
  deriving DecidableEq, Repr

abbrev Context := List Decl

inductive Lookup : Context → VarKind → Nat → TyExpr → USort → Prop where
  | here {Γ A s} :
      Lookup ({ kind := k, sort := s, ty := A } :: Γ) k 0
        ((if k = .ty then A.liftTyFrom 0 else A).liftTmFrom (if k = .tm then 0 else 1)) s
  | thereSame {Γ k n A s A' s'} :
      Lookup Γ k n A s →
      Lookup ({ kind := k, sort := s', ty := A' } :: Γ) k (n + 1)
        ((if k = .ty then A.liftTyFrom 0 else A).liftTmFrom (if k = .tm then 0 else 1)) s
  | thereOther {Γ k k' n A s A' s'} :
      k ≠ k' →
      Lookup Γ k n A s →
      Lookup ({ kind := k', sort := s', ty := A' } :: Γ) k n
        ((if k' = .ty then A.liftTyFrom 0 else A).liftTmFrom (if k' = .tm then 0 else 1)) s

inductive Sequent where
  | wf
  | hasSort : TyExpr → USort → Sequent
  | isCarrier : TyExpr → USort → Sequent
  | hasType : TmExpr → TyExpr → USort → Sequent
  | provable : TyExpr → Sequent
  deriving Repr

inductive Derives : Context → Sequent → Prop where
  | wfEmpty :
      Derives [] .wf
  | wfTmExtend {Γ A s} :
      Derives Γ .wf →
      Derives Γ (.hasSort A s) →
      Derives ({ kind := .tm, sort := s, ty := A } :: Γ) .wf
  | wfTyExtend {Γ C elemSort carrierSort} :
      Derives Γ .wf →
      Derives Γ (.hasSort C carrierSort) →
      Derives Γ (.isCarrier C elemSort) →
      Derives ({ kind := .ty, sort := elemSort, ty := C } :: Γ) .wf
  | sortAxiom {s t} :
      USort.axiomTarget? s = some t →
      Derives [] (.hasSort (.sort s) t)
  | sortCarrier {Γ s t} :
      Derives Γ .wf →
      USort.axiomTarget? s = some t →
      Derives Γ (.isCarrier (.sort s) s)
  | sortWeak {Γ d A s} :
      Derives Γ (.hasSort A s) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.hasSort
        ((if d.kind = .ty then A.liftTyFrom 0 else A).liftTmFrom (if d.kind = .tm then 0 else 1)) s)
  | carrierWeak {Γ d C s} :
      Derives Γ (.isCarrier C s) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.isCarrier
        ((if d.kind = .ty then C.liftTyFrom 0 else C).liftTmFrom (if d.kind = .tm then 0 else 1)) s)
  | typeWeak {Γ d t A s} :
      Derives Γ (.hasType t A s) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.hasType
        ((if d.kind = .tm then t.liftTmFrom 0 else t).liftTyFrom (if d.kind = .ty then 0 else 1))
        ((if d.kind = .ty then A.liftTyFrom 0 else A).liftTmFrom (if d.kind = .tm then 0 else 1)) s)
  | propWeak {Γ d P} :
      Derives Γ (.provable P) →
      Derives (d :: Γ) .wf →
      Derives (d :: Γ) (.provable
        ((if d.kind = .ty then P.liftTyFrom 0 else P).liftTmFrom (if d.kind = .tm then 0 else 1)))
  | tyVar {Γ i A s} :
      Derives Γ .wf →
      Lookup Γ .ty i A s →
      Derives Γ (.hasSort (.var i) s)
  | tmVar {Γ i A s} :
      Derives Γ .wf →
      Lookup Γ .tm i A s →
      Derives Γ (.hasType (.var i) A s)
  | prodFormTm {Γ s A B s₂ s₃} :
      Derives Γ (.hasSort A s) →
      Derives ({ kind := .tm, sort := s, ty := A } :: Γ) (.hasSort B s₂) →
      USort.prodResult? s s₂ = some s₃ →
      Derives Γ (.hasSort (.prod .tm s A B) s₃)
  | prodFormTy {Γ elemSort carrierSort C B bodySort resultSort} :
      Derives Γ (.hasSort C carrierSort) →
      Derives Γ (.isCarrier C elemSort) →
      Derives ({ kind := .ty, sort := elemSort, ty := C } :: Γ) (.hasSort B bodySort) →
      USort.prodResult? carrierSort bodySort = some resultSort →
      Derives Γ (.hasSort (.prod .ty elemSort C B) resultSort)
  | lamIntro {Γ s A body B s₂ s₃} :
      Derives Γ (.hasSort (.prod .tm s A B) s₃) →
      Derives ({ kind := .tm, sort := s, ty := A } :: Γ) (.hasType body B s₂) →
      Derives Γ (.hasType (.lam s A body) (.prod .tm s A B) s₃)
  | appElim {Γ fn arg domainSort A B functionSort bodySort} :
      Derives Γ (.hasType fn (.prod .tm domainSort A B) functionSort) →
      Derives Γ (.hasType arg A domainSort) →
      Derives Γ (.hasSort (B[arg]tm) bodySort) →
      Derives Γ (.hasType (.app fn arg) (B[arg]tm) bodySort)
  | typeConv {Γ t A B s} :
      Derives Γ (.hasType t A s) →
      Derives Γ (.hasSort B s) →
      A ≃β B →
      Derives Γ (.hasType t B s)
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
      Derives ({ kind := .tm, sort := .set i, ty := A } :: Γ) (.hasSort P .prop) →
      Derives Γ (.hasType (.subset (.set i) A P) (.power A) (.set i))
  | predForm {Γ A B t i} :
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.hasType t A (.set i)) →
      Derives Γ (.hasSort (.pred A B t) .prop)
  | typeLiftForm {Γ A B i} :
      Derives Γ (.hasSort A (.set i)) →
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.hasSort (.typeLift A B) (.set i))
  | typeLiftIntro {Γ t A B i} :
      Derives Γ (.hasType t A (.set i)) →
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.provable (.pred A B t)) →
      Derives Γ (.hasType t (.typeLift A B) (.set i))
  | typeLiftWeak {Γ t A B i} :
      Derives Γ (.hasType t (.typeLift A B) (.set i)) →
      Derives Γ (.hasSort A (.set i)) →
      Derives Γ (.hasType B (.power A) (.set i)) →
      Derives Γ (.hasType t A (.set i))
  | subsetProp {Γ t A B i} :
      Derives Γ (.hasType t (.typeLift A B) (.set i)) →
      Derives Γ (.hasType B (.power A) (.set i)) →
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
      Derives ({ kind := .tm, sort := .set i, ty := A } :: Γ) (.hasSort P .prop) →
      Derives Γ (.provable (P[a]tm)) →
      Derives Γ (.provable (P[b]tm))
  | existsForm {Γ A i} :
      Derives Γ (.hasSort A (.set i)) →
      Derives Γ (.hasSort (.exists_ A) .prop)
  | existsIntro {Γ e A i} :
      Derives Γ (.hasType e A (.set i)) →
      Derives Γ (.provable (.exists_ A))
  | takeSet {Γ X T f i} :
      Derives Γ (.hasSort X (.set i)) →
      Derives Γ (.hasSort T (.set i)) →
      Derives Γ (.hasType f (.prod .tm (.set i) X (T.liftTmFrom 0)) (.set i)) →
      Derives Γ (.provable (.exists_ X)) →
      Derives Γ (.provable
        (.prod .tm (.set i) X
          (.prod .tm (.set i) (X.liftTmFrom 0)
            (.equal
              (.app (f.liftTmFrom 0 |>.liftTmFrom 0) (.var 1))
              (.app (f.liftTmFrom 0 |>.liftTmFrom 0) (.var 0)))))) →
      Derives Γ (.hasType (.take X T f) T (.set i))
  | takeProp {Γ X T f i} :
      Derives Γ (.hasSort X (.set i)) →
      Derives Γ (.hasSort T .prop) →
      Derives Γ (.hasType f (.prod .tm (.set i) X (T.liftTmFrom 0)) .prop) →
      Derives Γ (.provable (.exists_ X)) →
      Derives Γ (.hasType (.take X T f) T .prop)
  | takeEq {Γ f t T X i} :
      Derives Γ (.hasType (.take X T f) T (.set i)) →
      Derives Γ (.hasType f (.prod .tm (.set i) X (T.liftTmFrom 0)) (.set i)) →
      Derives Γ (.hasType t X (.set i)) →
      Derives Γ (.provable (.equal (.take X T f) (.app f t)))

def WF (Γ : Context) : Prop := Derives Γ Sequent.wf
def HasSort (Γ : Context) (A : TyExpr) (s : USort) : Prop := Derives Γ (Sequent.hasSort A s)
def IsCarrier (Γ : Context) (C : TyExpr) (s : USort) : Prop := Derives Γ (Sequent.isCarrier C s)
def HasType (Γ : Context) (t : TmExpr) (A : TyExpr) (s : USort) : Prop := Derives Γ (Sequent.hasType t A s)
def Provable (Γ : Context) (P : TyExpr) : Prop := Derives Γ (Sequent.provable P)

notation:max "|- " Γ => WF Γ
notation:55 Γ " |- " A " :: " s => HasSort Γ A s
notation:55 Γ " |- " C " <= " s => IsCarrier Γ C s
notation:55 Γ " |- " t " : " A " :: " s => HasType Γ t A s
notation:55 Γ " |- " t " : " A => ∃ s, HasType Γ t A s
notation:55 Γ " |= " P => Provable Γ P

theorem falsePropFormed : HasSort [] falseProp USort.prop := by
  have hwf : |- ([] : Context) := Derives.wfEmpty
  have hcarrier : IsCarrier [] (TyExpr.sort USort.prop) USort.prop :=
    Derives.sortCarrier hwf rfl
  have hcarrierForm : HasSort [] (.sort .prop) .propKind :=
    Derives.sortAxiom rfl
  have hctx : |- ([{ kind := .ty, sort := .prop, ty := .sort .prop }] : Context) :=
    Derives.wfTyExtend hwf hcarrierForm hcarrier
  have hbody : HasSort [{ kind := .ty, sort := .prop, ty := .sort .prop }] (.var 0) USort.prop :=
    Derives.tyVar hctx Lookup.here
  exact Derives.prodFormTy hcarrierForm hcarrier hbody rfl

end RefType
