// For emacs: -*- fsharp -*-

module LHMachineTests

open NUnit.Framework
open LHMachine
open type LHMachine.Expr

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testTrivial () =
    let code = compile (ENum 0) [] (Map [])
    Assert.AreEqual( [Pushint 0], code );

[<Test>]
let testFactorial () =
    let eCode =
        EIf (EGt (EVar "n", ENum 0),
             EMul (EVar "n", EAp (EVar "fact", ESub (EVar "n", ENum 1))),
             ENum 1)
    let code = compile eCode [(0, "n")]
    // printfn "%A" code
    Assert.Pass()      

[<Test>]
let testFunc2Args () =
    // let sum n m = if (n > 0) then (n + sum (n - 1) m) else m
    let eCode =
        EIf (EGt (EVar "n", ENum 0),
             EAdd (EVar "n", EAp (EAp (EVar "sum", ESub (EVar "n", ENum 1)), EVar "m")),
             EVar "m")
    let code = (compile eCode [(1, "n"); (0, "m")] (Map [("sum", 2)])) @ [Slide 2]
    printfn "%A" code
    Assert.Pass()      
