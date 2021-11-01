module RefTools
open RefCore

  type PartialTree =
  | PComplete of JudgementTree
  | PTree of InferenceRule * Proposition * (PartialTree list)
  | PTask of Proposition

  type Constructor = Proposition -> Result<PartialTree , string>

  module Operator =

    type Present = Proposition * (PartialTree -> Result<PartialTree , string>)

    let HeadOf p =
      match p with
      | PComplete J -> Judgement.heads J
      | PTree (_ , P , _) -> P
      | PTask P -> P

    let rec AllTaskPresent : PartialTree -> (Present list) = fun p ->
      let propositionPresent : Proposition -> Present = fun p ->
        let f = fun t -> if Judgement.equiv (HeadOf t) p then Ok t else Error "Ilegal head"
        (p , f)
      match p with
      | PTree (_ , P , L) ->
        let l1 = List.fold List.append [] (List.map AllTaskPresent L)
        propositionPresent P :: l1
      | PTask P -> [propositionPresent P]
      | _ -> []

    let ConstPresentComposition : Constructor -> Present -> Result<PartialTree , string> = fun f p ->
      match p with
      | (P , g) ->
        match f P with
        | Ok t -> g t
        | Error err -> Error err

    let ApplyNth n : Constructor -> PartialTree -> Result<PartialTree , string> = fun c p ->
      if not(List.isEmpty (AllTaskPresent p)) then
        let p1 = List.item n (AllTaskPresent p)
        ConstPresentComposition c p1
      else Error "length error"

    let CtrNthComposition n : Constructor -> Constructor -> Constructor = fun c1 c2 p ->
      match (c1 p) with
      | Ok t ->
        ApplyNth n c2 t
      | _ -> Error "fail in c1"

    let ChallengeTwo : Constructor -> Constructor -> Constructor = fun c1 c2 p ->
      match (c1 p) with
      | Ok t -> Ok t
      | _ -> c2 p

  module Elementary =
    open Operator

    let ContextEmpty : Constructor = fun p ->
      match p with
      | CtxtJdg [] ->
        let comp = JTree (ContextEmpty , CtxtJdg [] , [])
        Ok (PComplete comp)
      | _ -> Error "Inappropriate"

    let ContextStart : Constructor = fun p ->
      match p with
      | CtxtJdg (CType (x , A) :: G) ->
        if not(Context.occur x G) then
          let task1 = PTask (CtxtJdg G)
          let task2 = PTask (TypeJdg (G , A , TSort TType))
          Ok (PTree (ContextStart x , p , [task1 ; task2]))
        else Error "Used Variable"
      | _ -> Error "Inappropriate"

    let ContextProp : Constructor = fun p ->
      match p with
      | CtxtJdg (CHold P :: G) ->
        let task1 = PTask (CtxtJdg G)
        let task2 = PTask (TypeJdg (G , P , TSort TProp))
        Ok (PTree (ContextProp , p , [task1 ; task2]))
      | _ -> Error "Inappropriate"
    
    let Axiom : Constructor = fun p ->
      match p with
      | TypeJdg ([] , TSort s1 , TSort s2) ->
        let comp = JTree (Axiom (s1 , s2) , p , [])
        Ok (PComplete comp)
      | _ -> Error "Inappropriate"

    let VariableOne : Constructor = fun p ->
      match p with
      | TypeJdg (CType (x1 , A1) :: G , TVar x2 , A2) ->
        if x1 = x2 && Alpha.equiv A1 A2 then
          if not (Context.occur x1 G) then
            let task1 = PTask (CtxtJdg G)
            let task2 = PTask (TypeJdg (G , A1 , TSort TType))
            Ok (PTree (Variable x1 , p , [task1 ; task2]))
          else Error "Used Variable"
        else Error "Not this variable"
      | _ -> Error "Inappropriate"

    let Weakning : Constructor = fun p ->
      match p with
      | TypeJdg (H :: G , t , A) ->
        let task1 = PTask (CtxtJdg (H :: G))
        let task2 = PTask (TypeJdg (G , t , A))
        Ok (PTree (WeakningType , p , [task1 ; task2]))
      | _ -> Error "Inappropriate"

    let rec VariableMany : Constructor = fun p ->
      match p with
      | TypeJdg (G , TVar x , A) when Context.occur x G ->
        ChallengeTwo VariableOne (CtrNthComposition 2 Weakning VariableMany) p
      | _ -> Error "Non occurrence"

    let rec ContextWellToType : Constructor = fun p ->
      match p with
      | TypeJdg _ -> ChallengeTwo ContextEmpty (ChallengeTwo ContextStart ContextProp) p
      | _ -> Error "not context judgement"