import RefType.Syntax

namespace RefType.Original

abbrev OSort := RefType.USort

inductive Expr where
  | sort : OSort → Expr
  | var : Nat → Expr
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
  .prod .propKind (.sort .prop) (.var 0)

end RefType.Original
