module Tests

open System
open Xunit
open RefCore
open RefTools

//freevalue
//[<FactAttribute>]
//let ``test freevalue1`` () =
//  let freeIs t l = Assert.True(Variable.freeValue t = l)
//  freeIs (TSort TType) []
//  freeIs (TVar 1) [1]
//  freeIs (TFun (1 , TSort TType , TVar 1)) []
//  freeIs (TFun (1 , TSort TType , TVar 2)) [2]
//  freeIs (TFun (1 , (TVar 2) , (TVar 1))) [2]
//  freeIs (TApp (TVar 1 , TVar 2)) [1 ; 2]

// fresh value
//[<FactAttribute>]
//let ``test freshvalue`` () =
//  let freshIs t l = Assert.True(Variable.freshValue t = l)
//  freshIs (TSort TType) 1
//  freshIs (TVar 1) 2
//  freshIs (TFun (1 , TSort TType , TVar 1)) 1
//  freshIs (TFun (1 , TSort TType , TVar 2)) 3
//  freshIs (TFun (1 , (TVar 2) , (TVar 1))) 3
//  freshIs (TApp (TVar 1 , TVar 2)) 3

// find
//[<FactAttribute>]
//let ``test find`` () =
//  let rec find x l =
//    match l with
//    | [] -> None
//    | (y , z) :: tail ->
//      if x = y then Some z else find x tail
//  Assert.True((find 1 [(1,2)]) = Some 2)

// alphaShift
//[<FactAttribute>]
//let ``test alphaShift`` () =
//  let alphashiftIs t1 i t2 = Assert.True(Alpha.strictEquiv (Alpha.alphaShift t1 i) t2)
//  alphashiftIs (TSort TType) 1 (TSort TType)
//  alphashiftIs (TVar 1) 2 (TVar 1)
//  alphashiftIs (TFun (1 , TSort TType , TVar 1)) 2 (TFun (2 , TSort TType , TVar 2))
//  alphashiftIs (TFun (1 , (TVar 2) , (TVar 1))) 3 (TFun (3 , (TVar 2) , (TVar 3)))
//  alphashiftIs (TApp (TVar 1 , TVar 2)) 3 (TApp (TVar 1 , TVar 2))
//  let t1e = (TFun (1 , TSort TType , TFun (1 , TSort TType , TVar 1)))
//  let t1r = (TFun (1 , TSort TType , TFun (2 , TSort TType , TVar 2)))
//  alphashiftIs t1e 1 t1r

// alphanormal
//[<FactAttribute>]
//let ``test alpha normalize`` () =
//  let alphanormalIs t1 t2 = Assert.True(Alpha.strictEquiv (Alpha.alphaNormalize t1) t2)
//  let t1e = (TFun (1 , TSort TType , TFun (1 , TSort TType , TApp (TVar 1 , TVar 3))))
//  let t1r = (TFun (4 , TSort TType , TFun (5 , TSort TType , TApp (TVar 5 , TVar 3))))
//  alphanormalIs t1e t1r
//  let alphaequiv t1 t2 = Assert.True(Alpha.equiv t1 t2)
//  alphaequiv (TFun (4 , TSort TType , TVar 4)) (TFun (5 , TSort TType , TVar 5))

// Judgement Valid
//[<Fact>]
//let ``My test`` () =
//  let prop1 = CtxtJdg []
//  let deri1 = JTree (ContextEmpty , prop1 , [])
//  let exampleResult = Judgement.isValidTree deri1
//  Assert.True(exampleResult)

// RefTools present
[<Fact>]
let ``try context empty`` () =
  let goaljudge = CtxtJdg []
  let tree = PTask goaljudge
  let res = Operator.ApplyNth 0 Elementary.ContextEmpty tree
//  Assert.False(List.isEmpty (Operator.AllTaskPresent tree))
//  let (prop , rest) = List.item 0 (Operator.AllTaskPresent tree)
//  let res1 = Elementary.ContextEmpty prop
//  match res1 with
//  | Ok (PComplete tree1) ->
//    match rest (PComplete tree1) with
//    | Ok (PComplete tree2) -> Assert.True(Judgement.isValidTree tree2)
//    | _ -> Assert.True(false)
//  | _ -> Assert.True(false)
  let s =
    if not(List.isEmpty (Operator.AllTaskPresent tree)) then
      let p1 = List.item 0 (Operator.AllTaskPresent tree)
      Operator.ConstPresentComposition Elementary.ContextEmpty p1
    else Error "canonical 1"

  match s with
  | Ok (PComplete tree3) -> ()
  | _ -> Assert.True(false)