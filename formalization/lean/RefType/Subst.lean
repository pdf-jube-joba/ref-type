import RefType.Syntax

namespace RefType

mutual

  def TyExpr.liftTyFrom (cutoff : Nat) (e : TyExpr) : TyExpr :=
    match e with
    | .sort s => .sort s
    | .var k => if cutoff ≤ k then .var (k + 1) else .var k
    | .prod kind s dom codom =>
        let dom' := dom.liftTyFrom cutoff
        let cutoff' := if kind = .ty then cutoff + 1 else cutoff
        .prod kind s dom' (codom.liftTyFrom cutoff')
    | .power base => .power (base.liftTyFrom cutoff)
    | .typeLift superset subsetTerm =>
        .typeLift (superset.liftTyFrom cutoff) (subsetTerm.liftTyFrom cutoff)
    | .pred superset subsetTerm elem =>
        .pred (superset.liftTyFrom cutoff) (subsetTerm.liftTyFrom cutoff) (elem.liftTyFrom cutoff)
    | .equal lhs rhs =>
        .equal (lhs.liftTyFrom cutoff) (rhs.liftTyFrom cutoff)
    | .exists_ base =>
        .exists_ (base.liftTyFrom cutoff)

  def TmExpr.liftTyFrom (cutoff : Nat) (e : TmExpr) : TmExpr :=
    match e with
    | .var k => .var k
    | .lam s ty body =>
        .lam s (ty.liftTyFrom cutoff) (body.liftTyFrom cutoff)
    | .app fn arg =>
        .app (fn.liftTyFrom cutoff) (arg.liftTyFrom cutoff)
    | .prove P =>
        .prove (P.liftTyFrom cutoff)
    | .subset s base predicate =>
        .subset s (base.liftTyFrom cutoff) (predicate.liftTyFrom cutoff)
    | .take X T f =>
        .take (X.liftTyFrom cutoff) (T.liftTyFrom cutoff) (f.liftTyFrom cutoff)

end

mutual

  def TyExpr.liftTmFrom (cutoff : Nat) (e : TyExpr) : TyExpr :=
    match e with
    | .sort s => .sort s
    | .var k => .var k
    | .prod kind s dom codom =>
        let dom' := dom.liftTmFrom cutoff
        let cutoff' := if kind = .tm then cutoff + 1 else cutoff
        .prod kind s dom' (codom.liftTmFrom cutoff')
    | .power base => .power (base.liftTmFrom cutoff)
    | .typeLift superset subsetTerm =>
        .typeLift (superset.liftTmFrom cutoff) (subsetTerm.liftTmFrom cutoff)
    | .pred superset subsetTerm elem =>
        .pred (superset.liftTmFrom cutoff) (subsetTerm.liftTmFrom cutoff) (elem.liftTmFrom cutoff)
    | .equal lhs rhs =>
        .equal (lhs.liftTmFrom cutoff) (rhs.liftTmFrom cutoff)
    | .exists_ base =>
        .exists_ (base.liftTmFrom cutoff)

  def TmExpr.liftTmFrom (cutoff : Nat) (e : TmExpr) : TmExpr :=
    match e with
    | .var k => if cutoff ≤ k then .var (k + 1) else .var k
    | .lam s ty body =>
        .lam s (ty.liftTmFrom cutoff) (body.liftTmFrom (cutoff + 1))
    | .app fn arg =>
        .app (fn.liftTmFrom cutoff) (arg.liftTmFrom cutoff)
    | .prove P =>
        .prove (P.liftTmFrom cutoff)
    | .subset s base predicate =>
        .subset s (base.liftTmFrom cutoff) (predicate.liftTmFrom (cutoff + 1))
    | .take X T f =>
        .take (X.liftTmFrom cutoff) (T.liftTmFrom cutoff) (f.liftTmFrom cutoff)

end

mutual

  def TyExpr.substTy (idx : Nat) (replacement : TyExpr) (e : TyExpr) : TyExpr :=
    match e with
    | .sort s => .sort s
    | .var k =>
        if _h : k = idx then
          replacement
        else if idx < k then
          .var (k - 1)
        else
          .var k
    | .prod kind s dom codom =>
        let dom' := TyExpr.substTy idx replacement dom
        if kind = .ty then
          .prod kind s dom' (TyExpr.substTy (idx + 1) (replacement.liftTyFrom 0) codom)
        else
          .prod kind s dom' (TyExpr.substTy idx replacement codom)
    | .power base => .power (TyExpr.substTy idx replacement base)
    | .typeLift superset subsetTerm =>
        .typeLift
          (TyExpr.substTy idx replacement superset)
          (TmExpr.substTy idx replacement subsetTerm)
    | .pred superset subsetTerm elem =>
        .pred
          (TyExpr.substTy idx replacement superset)
          (TmExpr.substTy idx replacement subsetTerm)
          (TmExpr.substTy idx replacement elem)
    | .equal lhs rhs =>
        .equal (TmExpr.substTy idx replacement lhs) (TmExpr.substTy idx replacement rhs)
    | .exists_ base =>
        .exists_ (TyExpr.substTy idx replacement base)
  termination_by sizeOf e

  def TmExpr.substTy (idx : Nat) (replacement : TyExpr) (e : TmExpr) : TmExpr :=
    match e with
    | .var k => .var k
    | .lam s ty body =>
        .lam s (TyExpr.substTy idx replacement ty) (TmExpr.substTy idx replacement body)
    | .app fn arg =>
        .app (TmExpr.substTy idx replacement fn) (TmExpr.substTy idx replacement arg)
    | .prove P =>
        .prove (TyExpr.substTy idx replacement P)
    | .subset s base predicate =>
        .subset s
          (TyExpr.substTy idx replacement base)
          (TyExpr.substTy idx replacement predicate)
    | .take X T f =>
        .take
          (TyExpr.substTy idx replacement X)
          (TyExpr.substTy idx replacement T)
          (TmExpr.substTy idx replacement f)
  termination_by sizeOf e

end

mutual

  def TyExpr.substTm (idx : Nat) (replacement : TmExpr) (e : TyExpr) : TyExpr :=
    match e with
    | .sort s => .sort s
    | .var k => .var k
    | .prod kind s dom codom =>
        let dom' := TyExpr.substTm idx replacement dom
        if kind = .tm then
          .prod kind s dom' (TyExpr.substTm (idx + 1) (replacement.liftTmFrom 0) codom)
        else
          .prod kind s dom' (TyExpr.substTm idx replacement codom)
    | .power base => .power (TyExpr.substTm idx replacement base)
    | .typeLift superset subsetTerm =>
        .typeLift
          (TyExpr.substTm idx replacement superset)
          (TmExpr.substTm idx replacement subsetTerm)
    | .pred superset subsetTerm elem =>
        .pred
          (TyExpr.substTm idx replacement superset)
          (TmExpr.substTm idx replacement subsetTerm)
          (TmExpr.substTm idx replacement elem)
    | .equal lhs rhs =>
        .equal (TmExpr.substTm idx replacement lhs) (TmExpr.substTm idx replacement rhs)
    | .exists_ base =>
        .exists_ (TyExpr.substTm idx replacement base)
  termination_by sizeOf e

  def TmExpr.substTm (idx : Nat) (replacement : TmExpr) (e : TmExpr) : TmExpr :=
    match e with
    | .var k =>
        if _h : k = idx then
          replacement
        else if idx < k then
          .var (k - 1)
        else
          .var k
    | .lam s ty body =>
        .lam s
          (TyExpr.substTm idx replacement ty)
          (TmExpr.substTm (idx + 1) (replacement.liftTmFrom 0) body)
    | .app fn arg =>
        .app (TmExpr.substTm idx replacement fn) (TmExpr.substTm idx replacement arg)
    | .prove P =>
        .prove (TyExpr.substTm idx replacement P)
    | .subset s base predicate =>
        .subset s
          (TyExpr.substTm idx replacement base)
          (TyExpr.substTm (idx + 1) (replacement.liftTmFrom 0) predicate)
    | .take X T f =>
        .take
          (TyExpr.substTm idx replacement X)
          (TyExpr.substTm idx replacement T)
          (TmExpr.substTm idx replacement f)
  termination_by sizeOf e

end

notation:70 A "[" t "]tm" => TyExpr.substTm 0 t A
notation:70 A "[" T "]ty" => TyExpr.substTy 0 T A
notation:70 t "[" u "]tm" => TmExpr.substTm 0 u t
notation:70 t "[" T "]ty" => TmExpr.substTy 0 T t

end RefType
