Require Import List Arith.
Open Scope list_scope.

Inductive Kind := KProp | KType.

Module Def.

Section Syntax.

Definition id := nat.

Inductive Term :=
  | TVar : id -> Term
  | TSort : Kind -> Term
  | TFor : id -> Term -> Term -> Term
  | TFun : id -> Term -> Term -> Term
  | TApp : Term -> Term -> Term
  | TRef : Term -> Term -> Term
  | TPrf : Term -> Term.

Inductive ContextSnippet :=
  | CType : id -> Term -> ContextSnippet
  | CHold : Term -> ContextSnippet.

Definition Context := list ContextSnippet.

End Syntax.

Section Operation.

Definition removeVal := remove Nat.eq_dec.
Fixpoint ListIn_dec x L :=
  match L with
  | nil => false
  | h :: L' =>
    if Nat.eqb x h then true else ListIn_dec x L'
  end.

Fixpoint FreeValueIn (M:Term) :=
  match M with
  | TVar x => x :: nil
  | TSort _ => nil
  | TFor x A B => removeVal x (FreeValueIn A) ++ (FreeValueIn B)
  | TFun x A t => removeVal x (FreeValueIn A) ++ (FreeValueIn t)
  | TApp M N => FreeValueIn M ++ FreeValueIn N
  | TRef A P => FreeValueIn A ++ FreeValueIn P
  | TPrf P => FreeValueIn P
  end.

Parameter Subst : Term -> id -> Term -> Term.
Parameter VarCase : forall x y N ,
  Subst (TVar x) y N = if Nat.eqb x y then N else TVar y.
Parameter SortCase : forall s y N , 
  Subst (TSort s) y N = TSort s.
Parameter ForCase : forall x A B y N ,
  if Nat.eqb x y then
    Subst (TFor x A B) y N = TFor x A B
  else if orb (negb (ListIn_dec x (FreeValueIn N))) (negb (ListIn_dec y (FreeValueIn B))) then
    Subst (TFor x A B) y N = TFor x A (Subst B y N)
  else
    exists z , andb (negb (ListIn_dec  z (FreeValueIn N))) (negb (ListIn_dec z (FreeValueIn B))) = true /\
    Subst (TFor x A B) y N = TFor z A (Subst (Subst B x (TVar z)) y N).
Parameter FunCase : forall x A B y N ,
  if Nat.eqb x y then
    Subst (TFun x A B) y N = TFun x A B
  else if orb (negb (ListIn_dec x (FreeValueIn N))) (negb (ListIn_dec y (FreeValueIn B))) then
    Subst (TFun x A B) y N = TFun x A (Subst B y N)
  else
    exists z , andb (negb (ListIn_dec  z (FreeValueIn N))) (negb (ListIn_dec z (FreeValueIn B))) = true /\
    Subst (TFun x A B) y N = TFun z A (Subst (Subst B x (TVar z)) y N).
Parameter AppCase : forall M1 M2 y N ,
  Subst (TApp M1 M2) y N = TApp (Subst M1 y N) (Subst M2 y N).
Parameter RefCase : forall M1 M2 y N ,
  Subst (TRef M1 M2) y N = TRef (Subst M1 y N) (Subst M2 y N).
Parameter PrfCase : forall P y N ,
  Subst (TPrf P) y N = TPrf (Subst P y N).

Inductive AlphaConv : Term -> Term -> Prop :=
  | ARenameFor : forall x A B y ,
    AlphaConv (TFor x A B) (TFor y A (Subst B x (TVar y)))
  | ARenameFun : forall x A B y ,
    AlphaConv (TFun x A B) (TFun y A (Subst B x (TVar y)))
  | ACongTFor1 : forall x A A' B ,
    AlphaConv A A' ->
    AlphaConv (TFor x A B) (TFor x A' B)
  | ACongTFor2 : forall x A B B' ,
    AlphaConv B B' ->
    AlphaConv (TFor x A B) (TFor x A B')
  | ACongTFun1 : forall x A A' B ,
    AlphaConv A A' ->
    AlphaConv (TFun x A B) (TFor x A' B)
  | ACongTFun2 : forall x A B B' ,
    AlphaConv B B' ->
    AlphaConv (TFun x A B) (TFor x A B')
  | ACongTApp1 : forall M M' N ,
    AlphaConv M M' ->
    AlphaConv (TApp M N) (TApp M' N)
  | ACongTApp2 : forall M N N' ,
    AlphaConv N N' ->
    AlphaConv (TApp M N) (TApp M N')
  | ACongTRef1 : forall M M' N ,
    AlphaConv M M' ->
    AlphaConv (TRef M N) (TRef M' N)
  | ACongTRef2 : forall M N N' ,
    AlphaConv N N' ->
    AlphaConv (TRef M N) (TRef M N')
  | ACongPrf : forall P P' ,
    AlphaConv P P' ->
    AlphaConv (TPrf P) (TPrf P')
  | ARefl : forall M ,
    AlphaConv M M
  | ASym : forall M N ,
    AlphaConv M N ->
    AlphaConv N M
  | ATrans : forall L M N ,
    AlphaConv L M ->
    AlphaConv M N ->
    AlphaConv L N.

Inductive BetaStep : Term -> Term -> Prop :=
  | BStep : forall x A M N ,
    BetaStep (TApp (TFun x A M) N) (Subst M x N)
  | BCongTFor1 : forall x A A' B ,
    BetaStep A A' ->
    BetaStep (TFor x A B) (TFor x A' B)
  | BCongTFor2 : forall x A B B' ,
    BetaStep B B' ->
    BetaStep (TFor x A B) (TFor x A B')
  | BCongTFun1 : forall x A A' B ,
    BetaStep A A' ->
    BetaStep (TFun x A B) (TFor x A' B)
  | BCongTFun2 : forall x A B B' ,
    BetaStep B B' ->
    BetaStep (TFun x A B) (TFor x A B')
  | BCongTApp1 : forall M M' N ,
    BetaStep M M' ->
    BetaStep (TApp M N) (TApp M' N)
  | BCongTApp2 : forall M N N' ,
    BetaStep N N' ->
    BetaStep (TApp M N) (TApp M N')
  | BCongTRef1 : forall M M' N ,
    BetaStep M M' ->
    BetaStep (TRef M N) (TRef M' N)
  | BCongTRef2 : forall M N N' ,
    BetaStep N N' ->
    BetaStep (TRef M N) (TRef M N')
  | BCongPrf : forall P P' ,
    BetaStep P P' ->
    BetaStep (TPrf P) (TPrf P').

Inductive BetaEq : Term -> Term -> Prop :=
  | Beta : forall M N ,
    BetaStep M N -> BetaEq M N
  | BRefl : forall M ,
    BetaEq M M
  | BSym : forall M N ,
    BetaEq M N -> BetaEq N M
  | BTrans : forall L M N ,
    BetaEq L M -> BetaEq M N ->
    BetaEq L N.

End Operation.

Section System.

Inductive ContextJudge : Context -> Type :=
  | Empty : ContextJudge nil
  | StartType : forall G A x s ,
    TypeJudge G A (TSort s) ->
    ContextJudge (cons (CType x A) G)
  | StartProp : forall G P ,
    TypeJudge G P (TSort KProp) ->
    ContextJudge (cons (CHold P) G)
with TypeJudge : Context -> Term -> Term -> Type :=
  | AxiomKind : TypeJudge nil (TSort KProp) (TSort KType)
  | Weakning : forall G t T h ,
    TypeJudge G t T ->
    ContextJudge (cons h G) ->
    TypeJudge (cons h G) t T
  | Variab : forall x A G , 
    ContextJudge (cons (CType x A) G) ->
    TypeJudge (cons (CType x A) G) (TVar x) A
  | ForForm : forall G x A B s1 s2 ,
    TypeJudge G A (TSort s1) ->
    TypeJudge (cons (CType x A) G) B (TSort s2) ->
    TypeJudge G (TFor x A B) (TSort s2)
  | ForIntro : forall G x A t B s ,
    TypeJudge G (TFor x A B) (TSort s) ->
    TypeJudge (cons (CType x A) G) t B ->
    TypeJudge G (TFun x A t) (TFor x A B)
  | ForElim : forall G M N x A B , 
    TypeJudge G M (TFor x A B) ->
    TypeJudge G N A ->
    TypeJudge G (TApp M N) (Subst B x M)
  | RefForm : forall G x A P ,
    TypeJudge G A (TSort KType) ->
    TypeJudge G P (TFor x A (TSort KProp)) ->
    TypeJudge G (TRef A P) (TSort KType)
  | RefIntro : forall G t A P ,
    TypeJudge G t A ->
    ProofJudge G (TApp P t) ->
    TypeJudge G t (TRef A P)
  | RefElim : forall G t A P ,
    TypeJudge G t (TRef A P) ->
    TypeJudge G t A
  | Conversion : forall G t A B s ,
    BetaEq A B ->
    TypeJudge G t A ->
    TypeJudge G B (TSort s) ->
    TypeJudge G t B
  | ProofAbstraction : forall G P ,
    ProofJudge G P ->
    TypeJudge G (TPrf P) P
with ProofJudge : Context -> Term -> Type :=
  | Assumption : forall G P ,
    ContextJudge (cons (CHold P) G) ->
    ProofJudge (cons (CHold P) G) P
  | ProofExistence : forall G P t ,
    TypeJudge G P (TSort KProp) ->
    TypeJudge G t P ->
    ProofJudge G P
  | RefInversion : forall G t A P ,
    TypeJudge G t (TRef A P) ->
    ProofJudge G (TApp P t).

End System.

End Def.