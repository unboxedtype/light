// For emacs: -*- fsharp -*-

module LHMachineTests

open NUnit.Framework
open LHMachine
open type LHMachine.Expr

[<SetUp>]
let Setup () =
    ()

let execAndCheck g ft expected =
    let gs = compileGlobals g ft
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename (generateFift gs)
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

[<Test>]
let testTrivial () =
    let code = compile (ENum 0) [] (Map [])
    Assert.AreEqual( [Pushint 0], code );

[<Test>]
let testFactorial () =
    let g = [("fact", ["n"],
                    EIf (EGt (EVar "n", ENum 1),
                         EMul (EVar "n", EAp (EVar "fact", ESub (EVar "n", ENum 1))),
                         ENum 1));
                   ("main", [], EAp (EVar "fact", ENum 5))]
    let ft = Map [("main", 0); ("fact", 1)]
    execAndCheck g ft "120"

[<Test>]
let testFunc2Args () =
    // let sum n m = if (n > 0) then (n + sum (n - 1) m) else m
    let g = [("sum", ["n";"m"],
                    EIf (EGt (EVar "n", ENum 0),
                         EAdd (EVar "n", EAp (EAp (EVar "sum", ESub (EVar "n", ENum 1)), EVar "m")),
                         EVar "m"));
                   ("main", [], EAp (EAp (EVar "sum", ENum 5), ENum 10))]
    let ft = Map [("main", 0); ("sum", 2)]
    execAndCheck g ft "25"

[<Test>]
let testGlobals () =
    let g = [("f", ["x"], ESub (EVar "x", ENum 1));
                   ("main", [], EAp (EVar "f", ENum 5))]
    let ft = Map [("main", 0); ("f", 1)]
    execAndCheck g ft "4"

[<Test>]
let testCurry1 () =
    let g = [("f", ["func"; "x"], EAp (EVar "func", EVar "x"));
                   ("inc", ["x"], EAdd (EVar "x", ENum 1));
                   ("main", [], EAp (EAp (EVar "f", EVar "inc"), ENum 1))]
    let ft = Map [("main", 0); ("f", 2); ("inc", 1); ("func", 1)]
    execAndCheck g ft "2"

[<Test>]
let testCurry2 () =
    let g =
        // f f1 f2 x y = f2 (f1 x) (f1 y)
        [("f", ["f1"; "f2"; "x"; "y"], EAp (EAp (EVar "f2", EAp (EVar "f1", EVar "x")), EAp (EVar "f1", EVar "y")));
         ("sum", ["x"; "y"], EAdd (EVar "x", EVar "y"));
         ("inc", ["x"], EAdd (EVar "x", ENum 1));
         ("main", [], EAp (EAp (EAp (EAp (EVar "f", EVar "inc"), EVar "sum"), ENum 10), ENum 20))]
    let ft = Map [("main", 0); ("f", 4); ("inc", 1); ("sum", 2); ("f1", 1); ("f2", 2)]
    execAndCheck g ft "32"

[<Test>]
let testArity0 () =
    let g =
        [("x1", [], ENum 10);
         ("main", [], EVar "x1")]
    let ft = Map [("main", 0); ("x1", 0)]
    execAndCheck g ft "10"

[<Test>]
let testPack0 () =
    let g =
        [("main", [], EPack (1, 2, [ENum 10; ENum 20]))]
    let ft = Map [("main", 0)]
    execAndCheck g ft "[ 1 [ 10 20 ] ]"

[<Test>]
let testPack1 () =
    let g =
        [("x1", [], ENum 10);
         ("x2", [], ENum 20);
         ("main", [], EPack (1, 2, [EVar "x1"; EVar "x2"]))]
    let ft = Map [("main", 0); ("x1", 0); ("x2", 0)]
    execAndCheck g ft "[ 1 [ 10 20 ] ]"

[<Test>]
let testPack2 () =
    let g =
        [("main", [], EPack (1, 0, []))]
    let ft = Map [("main", 0)]
    execAndCheck g ft "[ 1 [] ]"

[<Test>]
let testPack3 () =
    let g =
        [("main", [], EPack (1, 1, [EPack (2, 2, [EPack (3, 2, [ENum 10; ENum 20]);
                                                  EPack (4, 2, [ENum 50; ENum 60])])]))]
    let ft = Map [("main", 0)]
    execAndCheck g ft "[ 1 [ [ 2 [ [ 3 [ 10 20 ] ] [ 4 [ 50 60 ] ] ] ] ] ]"
