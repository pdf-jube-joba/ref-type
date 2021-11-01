module RefInteract
open RefCore 
open RefTools

  type Token =
    | LVar of int
    | LType | LProp | LFor | LFun | LApp | LRef | LPrf

  module Lexer =

    let separate (str : string) = List.ofArray (str.Split(' ' , '\n'))

    let parseInt (x : string) =
      match System.Int32.TryParse x with
      | true , v -> Some v
      | false , _ -> None
    let (|Int|_|) = parseInt

    let toToken str =
      match str with
      | "Type" -> Some LType
      | "Prop" -> Some LProp
      | "For" | "FormakeTerm" -> Some LFor
      | "Fun" | "\\" -> Some LFun
      | "App" | "@" -> Some LApp
      | "Ref" -> Some LRef
      | "Prf" -> Some LPrf
      | Int i -> Some (LVar i)
      | _ -> None

    let toMaybeTokenList str = List.map toToken (separate str)

    let toTokenList str =
      let l = toMaybeTokenList str
      let rec some =
        function
        | [] -> []
        | Some h :: tail -> h :: some tail
        | None :: tail -> some tail
      some l

  module Parser =

    let rec makeTerm l =
      let takeTwo tail =
        match makeTerm tail with
        | Some (term1 , remain1) ->
          match makeTerm remain1 with
          | Some (term2 , remain2) -> Some (term1 , term2 , remain2)
          | None -> None
        | None -> None
      match l with
      | [] -> None
      | LVar v :: tail -> Some (TVar v , tail)
      | LType :: tail -> Some (TSort TType , tail)
      | LProp :: tail -> Some (TSort TProp , tail)
      | LFor :: LVar v :: tail ->
        match takeTwo tail with
        | Some (term1 , term2 , remain) ->
          Some (TFor (v , term1 , term2) , remain)
        | None ->
          None
      | LFun :: LVar v :: tail ->
        match takeTwo tail with
        | Some (term1 , term2 , remain1) ->
          Some (TFun (v , term1 , term2) , remain1)
        | None ->
          None
      | LApp :: tail ->
        match takeTwo tail with
        | Some (term1 , term2 , remain) ->
          Some (TApp (term1 , term2) , remain)
        | None -> None
      | LRef :: tail ->
        match takeTwo tail with
        | Some (term1 , term2 , remain) ->
          Some (TApp (term1 , term2) , remain)
        | None -> None
      | LPrf :: tail ->
        match makeTerm tail with
        | Some (term1 , remain) ->
          Some (TPrf term1 , remain)
        | None -> None
      | _ ->
        None

    let oneTerm s =
      match s |> Lexer.toTokenList |> makeTerm with
      | Some (t , _) -> Some t
      | None -> None

  module Printing =

    type StringTree =
    | STree of string * list<StringTree>

    let printStringTree =
      let rec nbars n =
        if n <= 0 then "" else "-" + nbars (n - 1)
      let rec p n = 
        function
        | STree (str , list) ->
          let rem = List.map (p (1 + n)) list
          if List.isEmpty rem then
            nbars (n - 1) + "*" + str + "\n"
          else
            nbars n + str + "\n" + (List.reduce (+) rem)
      p 0

    let rec printTokenList =
      function
      | [] -> "end"
      | LVar i :: tail -> string i + " ; " + printTokenList tail
      | LType :: tail -> "Type" + " ; " + printTokenList tail
      | LProp :: tail -> "Prop" + " ; " + printTokenList tail
      | LFor :: tail -> "For" + " ; " + printTokenList tail
      | LFun :: tail -> "Fun" + " ; " + printTokenList tail
      | LApp :: tail -> "App" + " ; " + printTokenList tail
      | LRef :: tail -> "Ref" + " ; " + printTokenList tail
      | LPrf :: tail -> "Prf" + " ; " + printTokenList tail

    let rec printTerm =
      function
      | TVar x -> "Var" + string x
      | TSort TType -> "Type"
      | TSort TProp -> "Prop"
      | TFor (x , A , B) -> "For" + " " + string x + " " + "(" + printTerm A + ")" + "(" + printTerm B + ")"
      | TFun (x , A , t) -> "Fun" + " " + string x + " " + "(" +  printTerm A  + ")" + "(" +  printTerm t  + ")"
      | TApp (m , n) -> "App" + " " + printTerm m + printTerm n
      | TRef (a , p) -> "Ref" + " "+ printTerm a + printTerm p
      | TPrf p -> "Prf" + " " + printTerm p

    let rec printOutput =
      function
      | Some (t1 , l) -> printTerm t1 + " AND " + printTokenList l
      | None -> "Error"

    let rec printContext =
      function
      | [] -> "end"
      | CType (x , A) :: tail -> "type(" + string x + "," + printTerm A + ")," + printContext tail
      | CHold p :: tail -> "hold(" + printTerm p + "," + printContext tail

    let printProposition =
      function
      | CtxtJdg G -> "|-" + printContext G
      | TypeJdg (G , t , A) -> printContext G + "|-" + printTerm t + ":" + printTerm A
      | PropInf (G , A) -> printContext G + "|=" + printTerm A

    let printInference =
      function
      | ContextEmpty -> "ContexEmpty"
      | ContextStart x -> "ContextStart"
      | ContextProp -> "ContextProp"
      | Axiom _ -> "Axiom"
      | Variable x -> "Variable"
      | WeakningType -> "WeakningType"
      | ForForm -> "For form"
      | RefForm -> "Ref form"
      | Conversion _ -> "Conversion"
      | ForIntro -> "For intro"
      | ForElim -> "For elim"
      | RefIntro -> "Ref intro"
      | RefElim -> "Ref elim"
      | Assumption -> "Assumption"
      | WeakningProp -> "Weakning Prop"
      | ImplicitPrf -> "Implicit proof"
      | ExplicitPrf -> "Explicit proof"
      | RefInversion -> "Ref inversion"

    let rec ToStringTreeJudge =
      function
      | JTree (rule , prop , tree) ->
        let top = "Rule:" + printInference rule + "||Prop:" + printProposition prop
        STree (top , (List.map ToStringTreeJudge tree))

    let printJudgementTree = ToStringTreeJudge >> printStringTree

    let rec ToStringPartial =
      function
      | PComplete j ->
        match ToStringTreeJudge j with
        | STree (str , tree) -> STree ("[*]" + str , tree)
      | PTree (rule , prop , tree) ->
        let top = "[x]Rule:" + printInference rule + "--Prop:" + printProposition prop
        STree (top , (List.map ToStringPartial tree))
      | PTask p ->
        STree ("[-]" + printProposition p , [])

    let printPartialTree = ToStringPartial >> printStringTree

  module Interact =
    let nowContext : Context Ref = ref []
    let memory1 : option<Term> Ref = ref None
    let memory2 : option<Term> Ref = ref None
    let nowTree : option<PartialTree> Ref = ref None

    let unknownAction () =
      "unknown action" |> stdout.WriteLine
      ()
    let showContext () = Printing.printContext (! nowContext) |> stdout.WriteLine
    let showMemory () =
      let s1 =
        match ! memory1 with
        | Some t1 ->
          "memory1 : " + Printing.printTerm t1 + "\n"
        | None -> "memory1 is empty" + "\n"
      let s2 = 
        match ! memory2 with
        | Some t1 ->
          "memory2 : " + Printing.printTerm t1
        | None -> "memory2 is empty"
      s1 + s2 |> stdout.WriteLine
    let showGoal () =
      ( match ! nowTree with
        | Some tree ->
          let subgoals = List.map (fun (s,t) -> s) (Operator.AllTaskPresent tree)
          if List.isEmpty subgoals then "there is no goal" else 
            List.reduce (fun s1 s2 -> s1 + "\n" + s2) (List.map Printing.printProposition subgoals)
        | _ ->
          "tree is not registered")
      |> stdout.WriteLine
    let showTree () =
      ( match ! nowTree with
        | Some tree -> Printing.printPartialTree tree
        | None -> "tree is not registered"
      ) |> stdout.WriteLine

    module LexerOrParser =
      let toToken = Lexer.toTokenList >> Printing.printTokenList

      let toTerm =
        let f =
          function
          | Some t ->
            "success with" + (Printing.printTerm t)
          | None ->
            "fail to be term"
        Parser.oneTerm >> f

    module Memory =
      module Context =
        let pushType s =
          match s |> Parser.oneTerm with
          | Some t ->
            let fresh = Context.freshvalue (! nowContext)
            nowContext := CType (fresh , t) :: (! nowContext)
            "success."
          | None -> "fail to be term"
        let pushProp s =
          match s |> Parser.oneTerm with
          | Some t ->
            nowContext := CHold t :: (! nowContext)
            "success."
          | None -> "fail to be term"
        let popContext () = 
          match ! nowContext with
          | _ :: tail ->
            nowContext := tail
            "success."
          | [] ->
            "fail:not enough length"
      module Term =
        let stock s =
          match s |> Parser.oneTerm with
          | Some t ->
            memory2 := ! memory1
            memory1 := Some t
            "success."
          | None ->
            "fail to be term"

    module Proving =
      module Goal =
        let SetCtxtJdg () = 
          let tree = PTask (CtxtJdg ! nowContext)
          nowTree := Some tree
          "goal is setted"
        let SetTypeJdg () = 
          match ! memory1 , ! memory2 with
          | Some t1 , Some t2 ->
            let tree = PTask (TypeJdg (! nowContext , t1 , t2))
            nowTree := Some tree
            "goal is setted"
          | _ , _ ->
            "not enough term in memory"
        let SetPropJdg () =
          match ! memory1 with
          | Some t1 ->
            let tree = PTask (PropInf (! nowContext , t1))
            "goal is setted"
          | None -> "not enough term in memory"
        let Admitted () =
          nowTree := None
          "give up goal"
        let Exact () =
          match ! nowTree with
          | Some (PComplete J) ->
            if Judgement.isValidTree J then
              "completed"
            else
              "not valid tree"
          | Some _ -> "there exists not proved task"
          | _ -> "tree is not registered"
        let breakTree n c =
          match ! nowTree with
          | Some tree1 ->
            match Operator.ApplyNth n c tree1 with
            | Ok tree2 ->
              nowTree := Some tree2
              "success"
            | Error err -> err
          | None -> "tree is not registered"

    let searchAction =
      function
      | "#to-Token" ->
        printf ">"
        stdin.ReadLine () |> LexerOrParser.toToken |> stdout.WriteLine
      | "#to-Term" ->
        printf ">"
        stdin.ReadLine () |> LexerOrParser.toTerm |> stdout.WriteLine
      | "#show-context" -> showContext ()
      | "#show-memory" -> showMemory ()
      | "#show-goal" -> showGoal ()
      | "#show-tree" -> showTree () 
      | "#push-type" ->
        printf ">"
        stdin.ReadLine () |> Memory.Context.pushType |> stdout.WriteLine
      | "#push-prop" ->
        printf ">"
        stdin.ReadLine () |> Memory.Context.pushProp |> stdout.WriteLine
      | "#newtype" -> "Type" |> Memory.Context.pushType |> stdout.WriteLine
      | "#pop" -> () |> Memory.Context.popContext |> stdout.WriteLine
      | "#memory" ->
        printf ">"
        stdin.ReadLine () |> Memory.Term.stock |> stdout.WriteLine
      | "#prove-context-well" -> () |> Proving.Goal.SetCtxtJdg |> stdout.WriteLine
      | "#prove-type-judgement" -> () |> Proving.Goal.SetTypeJdg |> stdout.WriteLine
      | "#goal-exact" -> () |> Proving.Goal.Exact |> stdout.WriteLine
      | "#break-empty" -> (Proving.Goal.breakTree 0 Elementary.ContextEmpty) |> stdout.WriteLine
      | "#break-axiom" -> (Proving.Goal.breakTree 0 Elementary.Axiom) |> stdout.WriteLine
      | _ -> unknownAction ()

    let rec loop =
      function
      | "#quit" -> 0
      | c ->
        searchAction c
        printf ">"
        stdin.ReadLine () |> loop

  [<EntryPoint>]
  let main args =
    "!Welcome" |> stdout.WriteLine
    printf ">"
    stdin.ReadLine () |> Interact.loop