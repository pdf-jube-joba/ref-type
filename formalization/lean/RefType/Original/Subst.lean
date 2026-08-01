import RefType.Original.Syntax

namespace RefType.Original

def Expr.liftFrom (cutoff : Nat) : Expr → Expr
  | .sort s => .sort s
  | .var k => if cutoff ≤ k then .var (k + 1) else .var k
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
  | .var k =>
      if k = idx then replacement
      else if idx < k then .var (k - 1)
      else .var k
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

end RefType.Original
