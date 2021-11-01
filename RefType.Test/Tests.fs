module Tests

open System
open Xunit
open RefCore

[<Fact>]
let ``My test`` () =
    let exampleContextEmpty = CtxtJdg []
    let exampleDerivationOfContextEmpty = JTree (ContextEmpty , exampleContextEmpty , [])
    let exampleResult = Judgement.isValidTree exampleDerivationOfContextEmpty
    Assert.True(exampleResult)