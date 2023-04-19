// For emacs: -*- fsharp -*-

module LHMachineTests

open NUnit.Framework
open LHMachine
open type LHMachine.Expr

[<SetUp>]
let Setup () =
    ()

let execAndCheckPrint g expected ifPrint =
    let gs = compileGlobals g
    if ifPrint then
        printfn "%A" gs
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename (generateFift gs "" "" "")
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

let execAndCheck g expected =
    execAndCheckPrint g expected false

[<Test>]
let testTrivial () =
    let code = compile (ENum 0) []
    Assert.AreEqual( [Integer 0], code );

[<Test>]
let testFactorial () =
    let g = [("fact", [], EFunc ("n",
                           EIf (EGt (EVar "n", ENum 1),
                                EMul (EVar "n", EEval (EAp (EVar "fact", ESub (EVar "n", ENum 1)))),
                                      ENum 1)));
             ("main", [], EFunc ("", EEval (EAp (EVar "fact", ENum 5))))]
    execAndCheck g "120"

[<Test>]
let testFunc2Args () =
    // let sum n m = if (n > 0) then (n + sum (n - 1) m) else m
    let g = [("sum", [], EFunc ("n",
                          EFunc ("m",
                           EIf (EGt (EVar "n", ENum 0),
                                EAdd (EVar "n", EEval (EAp (EAp (EVar "sum", ESub (EVar "n", ENum 1)), EVar "m"))),
                                EVar "m"))));
             ("main", [], EFunc ("", EEval (EAp (EAp (EVar "sum", ENum 5), ENum 10))))]
    execAndCheck g "25"

[<Test>]
let testGlobals () =
    let g = [("f", [], EFunc ("x", ESub (EVar "x", ENum 1)));
             ("main", [], EFunc ("", EEval (EAp (EVar "f", ENum 5))))]
    execAndCheck g "4"

[<Test>]
let testCurry1 () =
    let g = [("f", [], EFunc ("func", EFunc ("x", EEval (EAp (EVar "func", EVar "x")))));
             ("inc", [], EFunc ("x", EAdd (EVar "x", ENum 1)));
             ("main", [], EFunc ("", EEval (EAp (EAp (EVar "f", EVar "inc"), ENum 1))))]
    execAndCheck g "2"

[<Test>]
let testCurry2 () =
    let g =
        // f f1 f2 x y = f2 (f1 x) (f1 y)
        [("f", [],
           EFunc ("f1",
            EFunc ("f2",
             EFunc ("x",
              EFunc ("y",
               EEval (
                EAp (EAp (EVar "f2", EEval (EAp (EVar "f1", EVar "x"))), EEval (EAp (EVar "f1", EVar "y")))
          ))))));

         ("sum", [], EFunc ("x", EFunc ("y", EAdd (EVar "x", EVar "y"))));
         ("inc", [], EFunc ("x", EAdd (EVar "x", ENum 1)));
         ("main", [], EFunc ("", EEval (EAp (EAp (EAp (EAp (EVar "f", EVar "inc"), EVar "sum"), ENum 10), ENum 20))))]
    execAndCheck g "32"

[<Test>]
let testArity0 () =
    let g =
        [("x1", [], ENum 10);
         ("main", [], EFunc ("", EVar "x1"))]
    execAndCheck g "10"

[<Test>]
let testPack0 () =
    let g =
        [("main", [], EFunc ("", EPack (1, 2, [ENum 10; ENum 20])))]
    execAndCheck g "[ 1 [ 10 20 ] ]"

[<Test>]
let testPack1 () =
    let g =
        [("x1", [], ENum 10);
         ("x2", [], ENum 20);
         ("main", [], EFunc ("", EPack (1, 2, [EVar "x1"; EVar "x2"])))]
    execAndCheck g "[ 1 [ 10 20 ] ]"

[<Test>]
let testPack2 () =
    let g =
        [("main", [], EFunc ("", EPack (1, 0, [])))]
    execAndCheck g "[ 1 [] ]"

[<Test>]
let testPack3 () =
    let g =
        [("main", [], EFunc ("", EPack (1, 1, [EPack (2, 2, [EPack (3, 2, [ENum 10; ENum 20]);                                                  EPack (4, 2, [ENum 50; ENum 60])])])))]
    execAndCheck g "[ 1 [ [ 2 [ [ 3 [ 10 20 ] ] [ 4 [ 50 60 ] ] ] ] ] ]"

[<Test>]
let testCase1 () =
    let g =
        [("some", [], EPack (0, 1, [EPack (1, 0, [])]));
         ("main", [], EFunc ("", ECase (EVar "some", [(0, ["x"], EVar "x")])))]
    execAndCheck g "[ 1 [] ]"

[<Test>]
let testCase2 () =
    let g =
        [("some", [], EPack (1, 2, [ENum 1; ENum 2]));
         ("main", [], EFunc ("",
                             ECase (EVar "some",
                                    [(0, ["x"], EVar "x");
                                     (1, ["x"; "y"], EAdd (EVar "x", EVar "y"))]))
          )
        ]
    execAndCheck g "3"

[<Test>]
let testChoice () =
    let g =
        [("first", [], EFunc ("n", EFunc ("m", EVar "n")));
         ("second", [], EFunc ("n", EFunc ("m", EVar "m")));
         ("main", [], EFunc ("", EEval (EAp (EAp (EVar "second", ENum 10), ENum 6))))]
    execAndCheck g "6"

[<Test>]
let testList1 () =
    let TNil = EPack (1, 0, [])
    let TCons x y = EPack (2, 2, [x; y])
    let myList = TCons (ENum 1) (TCons (ENum 2) (TCons (ENum 3) (TCons (ENum 4) (TCons (ENum 5) TNil))))
    let g =
        [("main", [], EFunc ("", myList))]
    execAndCheck g "[ 2 [ 1 [ 2 [ 2 [ 2 [ 3 [ 2 [ 4 [ 2 [ 5 [ 1 [] ] ] ] ] ] ] ] ] ] ] ]"

[<Test>]
let testListPatternMatch () =
    let TNil = EPack (1, 0, [])
    let TCons x y = EPack (2, 2, [x; y])
    let myList = TCons (ENum 1) (TCons (ENum 2) (TCons (ENum 3) (TCons (ENum 4) (TCons (ENum 5) TNil))))
    let g =
        [("mylist", [], myList);
         ("main", [],
          EFunc ("",
           ECase (EVar "mylist",
                 [(1, [], ENum 0);
                  (2, ["h"; "t"], EVar "h")])))]
    execAndCheck g "1"

[<Test>]
let testMapList () =
    // f n = n * 2
    // List.map f l =
    //   if l = [] then []
    //   else let h' = f (hd l)
    //        let t' = List.map f (tl l)
    //        h' :: t'
    // main = List.map f [1;2;3;4;5]
    let TNil = EPack (1, 0, [])
    let TCons x y = EPack (2, 2, [x; y])
    let myList = TCons (ENum 1) (TCons (ENum 2) (TCons (ENum 3) (TCons (ENum 4) (TCons (ENum 5) TNil))))
    let g =
        [("f", [], EFunc ("n", EMul (ENum 2, EVar "n")));
         ("List.map", [],
          EFunc ("fun",
           EFunc ("l",
             ECase (EVar "l",
                    [(1, [], TNil);
                     (2, ["h"; "t"],
                      (let h = EEval (EAp (EVar "fun", EVar "h"))
                       let t = EEval (EAp (EAp (EVar "List.map", EVar "fun"), EVar "t"))
                       TCons h t))]))));
         ("main", [], EFunc ("", EEval (EAp (EAp (EVar "List.map", EVar "f"), myList))))]
    execAndCheck g "[ 2 [ 2 [ 2 [ 4 [ 2 [ 6 [ 2 [ 8 [ 2 [ 10 [ 1 [] ] ] ] ] ] ] ] ] ] ] ]"

[<Test>]
let testLet1 () =
    let  g = [
        ("main", [], EFunc ("", ELet (false, [("t", ENum 3)], (EVar "t"))))
    ]
    execAndCheck g "3"

[<Test>]
let testLet2 () =
    let g = [
        ("main", [], EFunc ("", ELet (false, [("k", ENum 3); ("t", ENum 4)], EVar "t")))
    ]
    execAndCheck g "4"

[<Test>]
let testLet3 () =
    let g = [
        ("func", [],
          EFunc ("x",
           EFunc ("y",
            ELet (false, [("a", EVar "x"); ("b", EVar "y")], EAdd (EVar "a", EVar "b")))));
        ("main", [], EFunc ("", EEval (EAp (EAp (EVar "func", ENum 10), ENum 20))))
    ]
    execAndCheck g "30"

[<Test>]
let testLetRec1 () =
    let g = [
        ("main", [], EFunc ("", ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t")))
    ]
    execAndCheck g "3"

[<Test>]
let testLetRec2 () =
    let g = [
        ("main", [],
         EFunc ("", ELet (true, [("k", ENum 3);
                      ("t", EVar "k");
                      ("z", EAdd (EVar "t", EVar "k"))], EVar "z")))
    ]
    execAndCheck g "6"

[<Test>]
let testLetRec3 () =
    let g = [
        ("func1", [], ENum 3);
        ("func2", [], EFunc ("x", EAdd (EVar "x", ENum 10)));
        ("main", [],
         EFunc ("", ELet (true,
                          [("k", EEval (EAp (EVar "func2", EVar "func1")));
                           ("t", EVar "k");
                           ("z", EAdd (EVar "t", EVar "k"))],
                          EVar "z")))]
    execAndCheck g "26"

[<Test>]
let testFunc0 () =
    let g = [
        ("func1", [], EFunc ("x", EAdd (EVar "x", ENum 1)));
        ("main", [], EFunc ("", EEval (EAp (EVar "func1", ENum 100))))
    ]
    execAndCheck g "101"

[<Test>]
let testFunc1 () =
    let g = [("main", [], EFunc ("", EEval (EAp (EFunc ("n", EAdd (EVar "n", ENum 10)), ENum 10)))) ]
    execAndCheck g "20"

[<Test>]
let testFactorial2 () =
    let g = [("fact", [],
                    EFunc ("n",
                      EIf (EGt (EVar "n", ENum 1),
                           EMul (EVar "n", EEval (EAp (EVar "fact", ESub (EVar "n", ENum 1))) ),
                           ENum 1)));
             ("main", [], EFunc ("", EEval (EAp (EVar "fact", ENum 5))))]
    execAndCheck g "120"

[<Test>]
let testMax () =
    let g = [("max", [],
                    EFunc ("n",
                      EFunc ("m",
                        EIf (EGt (EVar "n", EVar "m"), EVar "n", EVar "m"))));
             ("main", [], EFunc ("", EEval (EAp (EAp (EVar "max", ENum 5), ENum 10)))) ]
    execAndCheck g "10"

[<Test>]
let testApply () =
    // apply f x = f x
    // main = apply (fun x -> x + 1) 100
    let g = [("apply", [],
                    EFunc ("f",
                      EFunc ("x", EEval (EAp (EVar "f", EVar "x")))));
             ("main", [],
                    EFunc ("",
                      EEval (EAp (EAp (EVar "apply", EFunc ("x", EAdd (EVar "x", ENum 1))),
                                  ENum 100))))]
    execAndCheck g "101"

[<Test>]
let testConst () =
    // const x = fun _ -> x
    // main = (const 100) 1   ---> evals to 100
    let g = [("const", [], EFunc ("x", EFunc ("", EVar "x")));
             ("main", [], EFunc ("", EEval (EAp (EAp (EVar "const", ENum 100), ENum 1))))]
    execAndCheck g "100"

[<Test>]
let testFunctionLine () =
    // add5 = fun x -> x + 5
    // mul2 = fun x -> x * 2
    // sub3 = fun x -> x - 3
    //
    // main =
    //   let fLine = [add5, mul2, sub3]
    //   List.fold (fun acc f -> f acc) 10 fLine
    // main --> (10 + 5) * 2 - 3 = 27

    let TNil = EPack (1, 0, [])
    let TCons x y = EPack (2, 2, [x; y])

    let fLine = ("fline",
                   TCons (EVar "add5") (TCons (EVar "mul2") (TCons (EVar "sub3") TNil)))
    let folder = EFunc ("acc", EFunc ("x", EEval (EAp (EVar "x", EVar "acc"))))
    let g = [("add5", [], EFunc ("x", EAdd (EVar "x", ENum 5)));
             ("mul2", [], EFunc ("x", EMul (EVar "x", ENum 2)));
             ("sub3", [], EFunc ("x", ESub (EVar "x", ENum 3)));
             ("fold", [],
               EFunc ("f",
                EFunc ("acc",
                 EFunc ("list",
                  ECase (EVar "list",
                    [(1, [], EVar "acc");
                     (2, ["h"; "t"],
                      (let acc' = EEval (EAp (EAp (EVar "f", EVar "acc"), EVar "h"))
                       EEval (EAp (EAp (EAp (EVar "fold", EVar "f"), acc'), EVar "t"))))])))));
             ("main", [],
               EFunc ("",
                ELet (false, [fLine],
                   EEval (EAp (EAp (EAp (EVar "fold", folder), ENum 10), EVar "fline")))));
        ]
    execAndCheck g "27"

[<Test>]
let testLetLet () =
    let g = [
        ("main", [],
         EFunc ("",
           ELet (false, [("k", ENum 3)],
            ELet (false, [("t", EVar "k")],
             ELet (false, [("z", EAdd (EVar "t", EVar "k"))], EVar "z")))))]
    execAndCheck g "6"


[<Test>]
let testFactLet () =
    // main =
    //  let rec fact n = if (n > 1) then n * fact (n - 1) else 1
    //  fact 5

    let simpleBody =
        EFunc ("n", ESub (EVar "n", ENum 1))
    let factBody =
        EFunc("fact'",
         EFunc("n",
          EIf (EGt (EVar "n", ENum 1),
               EMul (EVar "n",
                     EEval (EAp (EAp (EVar "fact'", EVar "fact'"), ESub (EVar "n", ENum 1)))),
               ENum 1)
         )
        )
    let mainBody =
        EEval (EAp (EAp (EVar "fact", EVar "fact"), EEval (EAp (EVar "simple", ENum 6))))

    let g =
        [("main", [],
          EFunc ("",
           ELet (false, [("fact", factBody)],
            ELet (false, [("simple", simpleBody)], mainBody))))]
    execAndCheck g "120"
