import RefType.Subst

namespace RefType

mutual

  inductive TyReduces : TyExpr → TyExpr → Prop where
    | prodDom {kind s dom dom' codom} :
        TyReduces dom dom' →
        TyReduces (.prod kind s dom codom) (.prod kind s dom' codom)
    | prodCodom {kind s dom codom codom'} :
        TyReduces codom codom' →
        TyReduces (.prod kind s dom codom) (.prod kind s dom codom')
    | power {base base'} :
        TyReduces base base' →
        TyReduces (.power base) (.power base')
    | predSubset {s base predicate elem} :
        TyReduces (.pred base (.subset s base predicate) elem) (predicate[elem]tm)
    | typeLiftLeft {superset superset' subsetTerm} :
        TyReduces superset superset' →
        TyReduces (.typeLift superset subsetTerm) (.typeLift superset' subsetTerm)
    | typeLiftRight {superset subsetTerm subsetTerm'} :
        TmReduces subsetTerm subsetTerm' →
        TyReduces (.typeLift superset subsetTerm) (.typeLift superset subsetTerm')
    | predLeft {superset superset' subsetTerm elem} :
        TyReduces superset superset' →
        TyReduces (.pred superset subsetTerm elem) (.pred superset' subsetTerm elem)
    | predMid {superset subsetTerm subsetTerm' elem} :
        TmReduces subsetTerm subsetTerm' →
        TyReduces (.pred superset subsetTerm elem) (.pred superset subsetTerm' elem)
    | predRight {superset subsetTerm elem elem'} :
        TmReduces elem elem' →
        TyReduces (.pred superset subsetTerm elem) (.pred superset subsetTerm elem')
    | equalLeft {lhs lhs' rhs} :
        TmReduces lhs lhs' →
        TyReduces (.equal lhs rhs) (.equal lhs' rhs)
    | equalRight {lhs rhs rhs'} :
        TmReduces rhs rhs' →
        TyReduces (.equal lhs rhs) (.equal lhs rhs')
    | exists_ {base base'} :
        TyReduces base base' →
        TyReduces (.exists_ base) (.exists_ base')

  inductive TmReduces : TmExpr → TmExpr → Prop where
    | beta {s ty body arg} :
        TmReduces (.app (.lam s ty body) arg) (body[arg]tm)
    | lamTy {s ty ty' body} :
        TyReduces ty ty' →
        TmReduces (.lam s ty body) (.lam s ty' body)
    | lamBody {s ty body body'} :
        TmReduces body body' →
        TmReduces (.lam s ty body) (.lam s ty body')
    | appFn {fn fn' arg} :
        TmReduces fn fn' →
        TmReduces (.app fn arg) (.app fn' arg)
    | appArg {fn arg arg'} :
        TmReduces arg arg' →
        TmReduces (.app fn arg) (.app fn arg')
    | prove {P P'} :
        TyReduces P P' →
        TmReduces (.prove P) (.prove P')
    | subsetBase {s base base' predicate} :
        TyReduces base base' →
        TmReduces (.subset s base predicate) (.subset s base' predicate)
    | subsetPred {s base predicate predicate'} :
        TyReduces predicate predicate' →
        TmReduces (.subset s base predicate) (.subset s base predicate')
    | takeDomain {X X' T f} :
        TyReduces X X' →
        TmReduces (.take X T f) (.take X' T f)
    | takeCodomain {X T T' f} :
        TyReduces T T' →
        TmReduces (.take X T f) (.take X T' f)
    | takeFunction {X T f f'} :
        TmReduces f f' →
        TmReduces (.take X T f) (.take X T f')

end

inductive TyBetaEq : TyExpr → TyExpr → Prop where
  | refl (A) : TyBetaEq A A
  | step : TyReduces A B → TyBetaEq A B
  | symm : TyBetaEq A B → TyBetaEq B A
  | trans : TyBetaEq A B → TyBetaEq B C → TyBetaEq A C

inductive TmBetaEq : TmExpr → TmExpr → Prop where
  | refl (t) : TmBetaEq t t
  | step : TmReduces t u → TmBetaEq t u
  | symm : TmBetaEq t u → TmBetaEq u t
  | trans : TmBetaEq t u → TmBetaEq u v → TmBetaEq t v

infix:50 " ⇒β " => TyReduces
infix:50 " ⇒β " => TmReduces
infix:50 " ≃β " => TyBetaEq
infix:50 " ≃β " => TmBetaEq

end RefType
