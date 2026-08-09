import RefType.BasicLemmas
import RefType.Original

namespace RefType

def mergedIndex : List VarKind → VarKind → Nat → Option Nat
  | [], _, _ => none
  | head :: tail, kind, index =>
      if head = kind then
        match index with
        | 0 => some 0
        | n + 1 => (mergedIndex tail kind n).map (· + 1)
      else
        (mergedIndex tail kind index).map (· + 1)

mutual

  inductive ErasesTy : List VarKind → TyExpr → Original.Expr → Prop where
    | sort : ErasesTy layout (.sort s) (.sort s)
    | var {s} :
        mergedIndex layout .ty i = some j →
        ErasesTy layout (.var i) (.var s j)
    | prodTm :
        ErasesTy layout A A₀ →
        ErasesTy (.tm :: layout) B B₀ →
        ErasesTy layout (.prod .tm s A B) (.prod s A₀ B₀)
    | prodTy :
        ErasesTy layout C C₀ →
        ErasesTy (.ty :: layout) B B₀ →
        ErasesTy layout (.prod .ty elemSort C B) (.prod carrierSort C₀ B₀)
    | power :
        ErasesTy layout A A₀ →
        ErasesTy layout (.power A) (.power A₀)
    | typeLift :
        ErasesTy layout A A₀ →
        ErasesTm layout B B₀ →
        ErasesTy layout (.typeLift A B) (.typeLift A₀ B₀)
    | pred :
        ErasesTy layout A A₀ →
        ErasesTm layout B B₀ →
        ErasesTm layout t t₀ →
        ErasesTy layout (.pred A B t) (.pred A₀ B₀ t₀)
    | equal :
        ErasesTm layout a a₀ →
        ErasesTm layout b b₀ →
        ErasesTy layout (.equal a b) (.equal a₀ b₀)
    | exists_ :
        ErasesTy layout A A₀ →
        ErasesTy layout (.exists_ A) (.exists_ A₀)

  inductive ErasesTm : List VarKind → TmExpr → Original.Expr → Prop where
    | var {s} :
        mergedIndex layout .tm i = some j →
        ErasesTm layout (.var i) (.var s j)
    | lam :
        ErasesTy layout A A₀ →
        ErasesTm (.tm :: layout) body body₀ →
        ErasesTm layout (.lam s A body) (.lam s A₀ body₀)
    | app :
        ErasesTm layout f f₀ →
        ErasesTm layout a a₀ →
        ErasesTm layout (.app f a) (.app f₀ a₀)
    | prove :
        ErasesTy layout P P₀ →
        ErasesTm layout (.prove P) (.prove P₀)
    | subset :
        ErasesTy layout A A₀ →
        ErasesTy (.tm :: layout) P P₀ →
        ErasesTm layout (.subset s A P) (.subset s A₀ P₀)
    | take :
        ErasesTy layout X X₀ →
        ErasesTy layout T T₀ →
        ErasesTm layout f f₀ →
        ErasesTm layout (.take X T f) (.take X₀ T₀ f₀)

end

def contextLayout (Γ : Context) : List VarKind := Γ.map (·.kind)

inductive ErasesContext : Context → Original.Context → Prop where
  | nil : ErasesContext [] []
  | tm :
      ErasesContext Γ Γ₀ →
      ErasesTy (contextLayout Γ) A A₀ →
      ErasesContext ({ kind := .tm, sort := s, ty := A } :: Γ)
        ({ sort := s, ty := A₀ } :: Γ₀)
  | ty :
      ErasesContext Γ Γ₀ →
      ErasesTy (contextLayout Γ) C C₀ →
      ErasesContext ({ kind := .ty, sort := elemSort, ty := C } :: Γ)
        ({ sort := carrierSort, ty := C₀ } :: Γ₀)

end RefType
