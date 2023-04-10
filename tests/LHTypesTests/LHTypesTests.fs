// For emacs: -*- fsharp -*-

module LHTypesTests

open NUnit.Framework

open LHTypes
open TVM
open type LHMachine.Expr

let execAndCheck g types dataCell expected =
    let stReader =
        stateReader types
        |> List.map TVM.instrToFift
        |> String.concat "\n"
    let stWriter =
        stateWriter types
        |> List.map TVM.instrToFift
        |> String.concat "\n"

    let gs = LHMachine.compileGlobalsWithTypes g types
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename (LHMachine.generateFift gs stReader stWriter dataCell)
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testStateGet0 () =
    let types = [("state", UserType "State");
                 ("State", LHTypes.PT [("x", (LHTypes.UInt 256));
                                       ("y", LHTypes.Bool);])]
    let dataCell = "<b 100 256 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("main", [], EFunc ("", EIf (ESelect (EVar "state", EVar "y"),
                                          EMul (ESelect (EVar "state", EVar "x"), ENum 2),
                                          ENum 0)))]
    execAndCheck g types dataCell "200"

[<Test>]
let testStateGet1 () =
    let types = [("state", UserType "State");
                 ("State", LHTypes.PT [("x", (LHTypes.UInt 256));
                                       ("y", LHTypes.Bool);])]
    let dataCell = "<b 100 256 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("main", [], EFunc ("",
                                 ELet (false, [("s", ESelect (EVar "state", EVar "y"))], EVar "s")))]
    execAndCheck g types dataCell "1"


[<Test>]
let testStateSet0 () =
    // update () = if state.y then (updateState ({ state with x = state.x * 2})) else ()
    // main () = let x = update () in state
    let types = [("state", UserType "State");
                 ("State", LHTypes.PT [("x", (LHTypes.UInt 64));
                                       ("y", LHTypes.Bool)])]
    let dataCell = "<b 100 64 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("update", [], EFunc ("",
                             EIf (ESelect (EVar "state", EVar "y"),
                                   EAssign (
                                   EUpdateRec (EVar "state", 0,
                                               EMul (ESelect (EVar "state", EVar "x"), ENum 2))),
                                  ENull)));
             ("main", [], EFunc ("", ELet (false, ["x", (EEval (EVar "update"))], EVar "state")))]
    execAndCheck g types dataCell "[ 0 [ 200 1 ] ]"

[<Test>]
let testStateFunction0 () =
    // update () = if state.y then (updateState ({ state with x = state.x * 2})) else ()
    // main () = let x = update () in state
    let types = [("state", LHTypes.UserType "State");
                 ("State", LHTypes.PT [("x", (UInt 64));
                                       ("y", Bool);
                                       ("fun", Function (UInt 64, UInt 64))])]
    let dataCell = "<b 100 64 u, 1 2 u, <{ INC }>s s>c ref,  b>"
    let g = [("state", [], ENull);  // this is a stub; will be replaced
             ("main", [], EFunc ("", EEval (EAp (ESelect (EVar "state", EVar "fun"), ENum 100))))]
    execAndCheck g types dataCell "101"
