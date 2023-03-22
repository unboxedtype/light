// For emacs: -*- fsharp -*-

module LHTypesTests

open NUnit.Framework

open LHTypes
open TVM
open type LHMachine.Expr

let execAndCheck g ft types dataCell expected =
    let stReader =
        stateReader types
        |> List.map TVM.instrToFift
        |> String.concat "\n"
    let stWriter =
        stateWriter types
        |> List.map TVM.instrToFift
        |> String.concat "\n"

    let gs = LHMachine.compileGlobals g ft
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename (LHMachine.generateFift gs stReader stWriter dataCell)
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testStateGet0 () =
    let types = [("State", LHTypes.PT [("x", (LHTypes.UInt 256));
                                       ("y", LHTypes.Bool);])]
    let dataCell = "<b 100 256 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("main", [], EIf (ESelect (EVar "state", 1),
                               EMul (ESelect (EVar "state", 0),
                                     ENum 2),
                               ENum 0))]
    let ft = Map [("main", 0); ("state", 0)]
    execAndCheck g ft types dataCell "200"

[<Test>]
let testStateGet1 () =
    let types = [("State", LHTypes.PT [("x", (LHTypes.UInt 256));
                                       ("y", LHTypes.Bool);])]
    let dataCell = "<b 100 256 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("main", [], ELet (false, [("s", ESelect (EVar "state", 1))], EVar "s"))]
    let ft = Map [("main", 0); ("state", 0)]
    execAndCheck g ft types dataCell "1"


[<Test>]
let testStateSet0 () =
    // update () = if state.y then (updateState ({ state with x = state.x * 2})) else ()
    // main () = let x = update () in state
    let types = [("State", LHTypes.PT [("x", (LHTypes.UInt 64));
                                       ("y", LHTypes.Bool)])]
    let dataCell = "<b 100 64 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("update", [], EIf (ESelect (EVar "state", 1),
                                 EUpdateState (EUpdateRec (EVar "state", 0,
                                                         EMul (ESelect (EVar "state", 0), ENum 2))),
                                 ENull));
             ("main", [], ELet (false, ["x", (EVar "update")], EVar "state"))]
    let ft = Map [("main", 0); ("state", 0); ("update", 0)]
    execAndCheck g ft types dataCell "[ 0 [ 200 1 ] ]"
