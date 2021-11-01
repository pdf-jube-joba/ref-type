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
      | [] -> "[]"
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

    module LexerOrParser =
      let toToken () =
        stdin.ReadLine () |> Lexer.toTokenList |> Printing.printTokenList |> stdout.WriteLine
        ()
      let toTerm () =
        match stdin.ReadLine () |> Parser.oneTerm with
        | Some t ->
          "success with" + (Printing.printTerm t) |> stdout.WriteLine
        | None ->
          "fail to be term" |> stdout.WriteLine
        ()
    
    module Memory =
      module Context =
        let show () =
          Printing.printContext (! nowContext) |> stdout.WriteLine
          ()
        let pushType () =
          match stdin.ReadLine () |> Lexer.parseInt with
          | Some i ->
            "var is " + string i |> stdout.WriteLine
            match stdin.ReadLine () |> Lexer.toTokenList |> Parser.makeTerm with
            | Some (t , l) ->
              nowContext := CType (i , t) :: ! nowContext
              "success" |> stdout.WriteLine
            | None -> "fail to be term" |> stdout.Write
          | _ -> "not variable" |> stdout.WriteLine
        let pushProp () =
          match stdin.ReadLine () |> Parser.oneTerm with
          | Some t ->
            nowContext := CHold t :: ! nowContext
            "success" |> stdout.WriteLine
          | None ->
            "fail to be term" |> stdout.WriteLine
        let pop () = 
          match ! nowContext with
          | [] -> "unable to pop" |> stdout.WriteLine
          | head :: tail ->
            nowContext := tail
            "success" |> stdout.WriteLine
      module Term =
        let show () =
          match ! memory1 with
          | Some t1 ->
            "memory1 : " + Printing.printTerm t1 |> stdout.WriteLine
          | None -> "memory1 is empty" |> stdout.WriteLine
          match ! memory2 with
          | Some t1 ->
            "memory2 : " + Printing.printTerm t1 |> stdout.WriteLine
          | None -> "memory2 is empty" |> stdout.WriteLine
        let stock () =
          match stdin.ReadLine () |> Parser.oneTerm with
          | Some t ->
            memory2 := ! memory1
            memory1 := Some t
          | None ->
            "fail to be term" |> stdout.WriteLine

    module Proving =
      module Goal =
        let SetCtxtJdg () = 
          let tree = PTask (CtxtJdg ! nowContext)
          nowTree := Some tree
          "set goal \n" + Printing.printPartialTree tree |> stdout.WriteLine
        let SetTypeJdg () = 
          match ! memory1 , ! memory2 with
          | Some t1 , Some t2 ->
            let tree = PTask (TypeJdg (! nowContext , t1 , t2))
            nowTree := Some tree
            "set goal to" + Printing.printPartialTree (tree) |> stdout.WriteLine
          | _ , _ ->
            "not enough term in memory" |> stdout.WriteLine
        let Exact () =
          match ! nowTree with
          | Some (PComplete J) ->
            if Judgement.isValidTree J then
              "completed" |> stdout.WriteLine
            else
              "not valid tree" |> stdout.WriteLine
          | _ -> "tree is not registered" |> stdout.WriteLine
        let ShowGoal () =
          match ! nowTree with
          | Some tree ->
            let goals = List.map (fun (s,t) -> s) (Operator.AllTaskPresent tree)
            let sgoals = List.map Printing.printProposition goals
            ignore (List.map (fun (s:string) -> s |> stdout.WriteLine) sgoals)
          | _ ->
            "tree is not registerd" |> stdout.WriteLine
        let ChallengeEmpty () =
          match ! nowTree with
          | Some tree ->
            let goals = List.map (fun (s,t) -> s) (Operator.AllTaskPresent tree)
            if List.isEmpty goals then
              "no goal" |> stdout.WriteLine
            else
              let chargeNum = stdin.Read ()
              match RefTools.Operator.ApplyNth chargeNum Elementary.CContextEmpty tree with
              | Ok t1 ->
                nowTree := Some t1
              | Error err -> err |> stdout.WriteLine
          | _ -> "tree is not registered" |> stdout.WriteLine

    let searchAction =
      function
      | "#toToken" ->  LexerOrParser.toToken
      | "#toTokenList" ->  LexerOrParser.toToken
      | "#toTerm" ->  LexerOrParser.toTerm
      | "#context-show" ->  Memory.Context.show
      | "#context-push-type" ->  Memory.Context.pushType
      | "#context-push-prop" ->  Memory.Context.pushProp
      | "#context-pop" ->  Memory.Context.pop
      | "#memory-show" ->  Memory.Term.show
      | "#memory-term" ->  Memory.Term.stock
      | "#prove-context-well" ->  Proving.Goal.SetCtxtJdg
      | "#prove-type-judgement" ->  Proving.Goal.SetTypeJdg
      | "#goal-show" -> Proving.Goal.ShowGoal
      | "#goal-exact" ->  Proving.Goal.Exact
      | "#goal-empty" -> Proving.Goal.ChallengeEmpty
      | _ -> unknownAction

    let rec loop =
      function
      | "#quit" -> 0
      | c ->
        "input is:" + c |> stdout.WriteLine
        searchAction c ()
        stdin.ReadLine () |> loop

  [<EntryPoint>]
  let main args =
    "Welcome" |> stdout.WriteLine
    stdin.ReadLine () |> Interact.loop