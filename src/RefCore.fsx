module RefCore =

  type Sort =
    | TProp | TType

  type Term =
    | TVar of int
    | TSort of Sort
    | TFor of int * Term * Term
    | TFun of int * Term * Term
    | TApp of Term * Term
    | TRef of Term * Term
    | TPrf of Term

  type ContextSnippet =
    | CType of int * Term
    | CHold of Term

  type Context = ContextSnippet list

  type BetaEqSeq = (Term * Term) list

  type Propotision =
  | CtxtJdg of Context
  | TypeJdg of Context * Term * Term
  | PropInf of Context * Term
  | BetaEqv of BetaEqSeq
  | NewVars of int

  type InferenceRule =
  | ContextEmpty
  | ContextStart
  | ContextProp
  | Axiom of Sort * Sort
  | Variable
  | WeakningType
  | ForForm
  | RefForm
  | Conversion
  | ForIntro
  | ForElim
  | RefIntro
  | RefElim
  | Assumption
  | WeakningProp
  | ImplicitPrf
  | ExplicitPrf
  | RefInversion

  module Variable =

    let rec freeValue l =
      let rec remove x l =
        match l with
        | [] -> []
        | y :: t ->
          let tail = remove x t in if x = y then tail else x :: tail

      match l with
      | TVar x -> [x]
      | TSort s -> []
      | TFor (x , M1 , M2) -> (freeValue M1) @ (remove x (freeValue M2))
      | TFun (x , M1 , M2) -> (freeValue M1) @ (remove x (freeValue M2))
      | TApp (M1 , M2) -> (freeValue M1) @ (freeValue M2)
      | TRef (M1 , M2) -> (freeValue M1) @ (freeValue M2)
      | TPrf M1 -> (freeValue M1)

    let freshValue m = 1 + (List.fold max 0 (freeValue m))

  module Alpha =

    let alphaShift =
      let rec find x l =
        match l with
        | [] -> None
        | (y , z) :: tail ->
          if x = y then Some z else find x tail
      let rec alpha term fresh change =
        match term with
        | TVar x ->
          match find x change with
          | Some z -> TVar z
          | _ -> TVar x
        | TSort s -> TSort s
        | TFor (x , M1 , M2)  -> TFor (fresh , (alpha M1 (1 + fresh) change) , (alpha M1 (1 + fresh) ((x , fresh) :: change)))
        | TFun (x , M1 , M2) -> TFun (fresh , (alpha M1 (1 + fresh) change) , (alpha M1 (1 + fresh) ((x , fresh) :: change)))
        | TApp (M1 , M2) -> TApp ((alpha M1 fresh change) , (alpha M2 fresh change))
        | TRef (M1 , M2) -> TRef ((alpha M1 fresh change) , (alpha M2 fresh change))
        | TPrf M1 -> TPrf (alpha M1 fresh change)
      fun m x -> alpha m x []
    
    let alphaNormalize m =
      let rec find x l =
        match l with
        | [] -> false
        | head :: tail ->
          if x = head then true else find x tail
      let rec reset m s l =
        match m with
        | TVar x ->
          if find x l then TVar (x - s) else TVar x
        | TSort s -> TSort s
        | TFor (x , M1 , M2) -> TFor (x - s , reset M1 s l , reset M2 s (x :: l))
        | TFun (x , M1 , M2) -> TFun (x - s , reset M1 s l , reset M2 s (x :: l))
        | TApp (M1 , M2) -> TApp (reset M1 s l , reset M2 s l)
        | TRef (M1 , M2) -> TRef (reset M1 s l , reset M2 s l)
        | TPrf M1 -> TPrf (reset M1 s l)
      let fresh = Variable.freshValue m
      reset (alphaShift m fresh) fresh []

    let equiv m1 m2 =
      let rec strictEquiv m1 m2 =
        match m1 , m2 with
        | TVar x1 , TVar x2 -> x1 = x2
        | TSort TProp , TSort TProp -> true
        | TSort TType , TSort TType -> true
        | TFor (x1 , m1 , n1) , TFor (x2 , m2 , n2) ->
          x1 = x2 && (strictEquiv m1 m2) && (strictEquiv m2 n2)
        | TFun (x1 , m1 , n1) , TFun (x2 , m2 , n2) ->
          x1 = x2 && (strictEquiv m1 m2) && (strictEquiv m2 n2)
        | TApp (m1 , n1) , TApp (m2 , n2) ->
          (strictEquiv m1 m2) && (strictEquiv n1 n2)
        | TRef (m1 , n1) , TRef (m2 , n2) ->
          (strictEquiv m1 m2) && (strictEquiv n1 n2)
        | TPrf m1 , TPrf m2 -> strictEquiv m1 m2
        | _ , _ -> false
      strictEquiv (alphaNormalize m1) (alphaNormalize m2)

  module Context =
    let snipEquiv g1 g2 =
      match g1 , g2 with
      | CType (x1 , t1) , CType (x2 , t2) -> x1 = x2 && Alpha.equiv t1 t2
      | CHold p1 , CHold p2 -> Alpha.equiv p1 p2
      | _ , _ -> false

    let rec occur x g =
      match g with
      | [] -> true
      | CType (y , t) :: g2 ->
        if x = y then true else occur x g2
      | CHold p :: g2 -> occur x g2

    let rec equiv g1 g2 =
      match g1 , g2 with
      | [] , [] -> true
      | h1 :: t1 , h2 :: t2 -> snipEquiv h1 h2 && equiv g1 g2
      | _ , _ -> false
    
    let rec equivAll (gs : Context list) = // = fold 単位元がわからなかった
      match gs with
      | [] -> true
      | [gh1] -> true 
      | gh1 :: gh2 :: gt -> (equiv gh1 gh2) && (equivAll (gh2 :: gt))

  module Beta =
    let subst m x n =
      let rec simpleSubst m x n =
        match m with
        | TVar y -> if x = y then n else TVar y
        | TSort s -> TSort s
        | TFor (y , M1 , M2) ->
          if x = y then TFor (x , (simpleSubst M1 x n) , M2) else TFor (x , (simpleSubst M1 x n) , (simpleSubst M2 x n))
        | TFun (y , M1 , M2) ->
          if x = y then TFun (x , (simpleSubst M1 x n) , M2) else TFun (x , (simpleSubst M1 x n) , (simpleSubst M2 x n))
        | TApp (M1 , M2) -> TApp (simpleSubst M1 x n , simpleSubst M2 x n)
        | TRef (M1 , M2) -> TRef (simpleSubst M1 x n , simpleSubst M2 x n)
        | TPrf M1 -> TPrf (simpleSubst M1 x n)
      let shiftM m n = Alpha.alphaShift m (Variable.freshValue n)
      Alpha.alphaNormalize (simpleSubst (shiftM m n) x n)

    let rec isNormal m = // <=> ! is reducible
      match m with
      | TVar _ -> true
      | TSort s -> true
      | TFor (x , M1 , M2) -> isNormal M1 && isNormal M2
      | TFun (x , M1 , M2) -> isNormal M1 && isNormal M2
      | TApp (TVar _ , M2) -> isNormal M2
      | TApp _ -> false
      | TRef (M1 , M2) -> isNormal M1 && isNormal M2
      | TPrf M1 -> isNormal M1

    let rec oneStep m =
      match m with
      | TVar x -> TVar x
      | TSort s -> TSort s
      | TFor (x , M1 , M2) -> TFor (x , oneStep M1 , oneStep M2)
      | TFun (x , M1 , M2) -> TFun (x , oneStep M1 , oneStep M2)
      | TApp (TFun (x , M1 , M2) , M3) -> subst M2 x M3
      | TApp (M1 , M2) -> TApp (oneStep M1 , oneStep M2)
      | TRef (M1 , M2) -> TRef (oneStep M1 , oneStep M2)
      | TPrf M1 -> TPrf (oneStep M1)

    let beginOf l =
      match l with
      | [] -> None
      | (t1 , _) :: _ -> Some t1
    let rec endOf l =
      match l with
      | [] -> None
      | [(_ , t2)] -> Some t2
      | _ :: tail -> endOf tail
 
    let rec isAcc l =
      match l with
      | [] -> true
      | (t1 , t2) :: tail ->
        (Alpha.equiv t1 t2 || Alpha.equiv (oneStep t1) t2 || Alpha.equiv t1 (oneStep t2)) && isAcc tail

    let betaEquiv m1 m2 = // may no be terminate dont use
      let rec reduction m =
        if isNormal m then m else reduction m
      Alpha.equiv (reduction m1) (reduction m2)

  module Judgement =
    let derivation : InferenceRule -> Propotision list -> Propotision option = fun d l ->
      match d , l with
      | ContextEmpty , [] -> Some (CtxtJdg [])
      | ContextStart , [CtxtJdg G1 ; TypeJdg (G2 , A , TSort TType) ; NewVars x] ->
        if Context.equiv G1 G2 && not(Context.occur x G1) then
          Some (CtxtJdg (CType (x , A) :: G1))
        else None
      | ContextProp , [CtxtJdg G1 ; TypeJdg (G2 , P , TSort TProp)] ->
        if Context.equiv G1 G2 then
          Some (CtxtJdg (CHold P :: G1))
         else None
      | Axiom (s1 , s2) , [] -> Some (TypeJdg ([] , TSort s1 , TSort s2))
      | Variable , [CtxtJdg G1 ; TypeJdg (G2 , A , TSort TType) ; NewVars x] ->
        if Context.equiv G1 G2 && not(Context.occur x G1) then
          Some (TypeJdg (CType (x , A) :: G1 , TVar x , A))
        else None
      | WeakningType , [CtxtJdg (s1 :: G1) ; TypeJdg (G2 , t , A)] ->
        if Context.equiv G1 G2 then
          Some (TypeJdg (s1 :: G1 , t , A))
        else None
      | ForForm , [TypeJdg (G1 , A1 , TSort s1) ; TypeJdg ((CType (x , A2) :: G2) , A3 , TSort s2 ) ] ->
        if Context.equiv G1 G2 && Alpha.equiv A1 A2 then
          Some (TypeJdg (G1 , TFor (x , A2 , A3) , TSort s2))
        else None
      | RefForm , [TypeJdg (G1 , A1 , TSort TType) ; TypeJdg (G2 , P , TFor (x , A2 , TSort TProp))] ->
        if Context.equiv G1 G2 && Alpha.equiv A1 A2 then
          Some (TypeJdg (G1 , TRef (A1 , P) , TSort TType))
        else None
      | Conversion , [TypeJdg (G1 , x , A1) ; BetaEqv L ; TypeJdg (G2 , A2 , TSort _)] ->
        if Context.equiv G1 G2 && Beta.isAcc L then
          match Beta.beginOf L , Beta.endOf L with
          | Some t1 , Some t2 ->
            if Alpha.equiv t1 A1 && Alpha.equiv t2 A2 then Some (TypeJdg (G1 , x , A2)) else None
          | _ , _ -> None
        else None
      | ForIntro , [TypeJdg (CType (x1 , A1) :: G1 , t , A2) ; TypeJdg (G2 , TFor (x2 , A3 , A4) , TSort _)] ->
        if Context.equiv G1 G2 && Alpha.equiv A1 A3 && Alpha.equiv A2 A4 && x1 = x2 then
          Some (TypeJdg (G1 , TFun (x1 , A1 , t) , TFor (x1 , A1 , A2)))
        else None
      | ForElim , [TypeJdg (G1 , t1 , TFor (x , A1 , A2)) ; TypeJdg (G2 , t2 , A3)] ->
        if Context.equiv G1 G2 && Alpha.equiv A1 A3 then
          Some (TypeJdg (G1 , TApp (t1 , t2) , Beta.subst A2 x t2))
        else None
      | RefIntro , [TypeJdg (G1 , t1 , A1) ; TypeJdg (G2 , TRef (A2 , P1) , TSort TType) ; PropInf (G3 , TApp (P2 , t2))] ->
        if Context.equiv G1 G2 && Context.equiv G2 G3 && Alpha.equiv A1 A2 && Alpha.equiv P1 P2 && Alpha.equiv t1 t2 then
          Some (TypeJdg (G1 , t1 , TRef (A1 , P1)))
         else None
      | RefElim , [TypeJdg (G , t , TRef (A , P))] -> Some (TypeJdg (G , t , A))
      | Assumption , [CtxtJdg ((CHold P) :: G)] -> Some (PropInf ((CHold P) :: G , P))
      | WeakningProp , [PropInf (G1 , P) ; CtxtJdg (s1 :: G2)] -> Some (PropInf (s1 :: G2 , P))
      | ImplicitPrf , [TypeJdg (G1 , P1 , TSort TProp) ; TypeJdg (G2 , t , P2)] ->
        if Context.equiv G1 G2 && Alpha.equiv P1 P2 then
          Some (PropInf (G1 , P1))
        else None
      | ExplicitPrf , [TypeJdg (G1 , P1 , TSort TProp) ; PropInf (G2 , P2)] ->
        if Context.equiv G1 G2 && Alpha.equiv P1 P2 then
          Some (TypeJdg (G1 , TPrf P1 , P1))
        else None
      | RefInversion , [TypeJdg (G , t , TRef (A , P))] -> Some (PropInf (G , TApp (P , t)))
      | _ , _ -> None
