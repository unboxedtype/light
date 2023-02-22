module GMachineTests

open NUnit.Framework
open System
open System.Collections.Generic
open GMachine

[<OneTimeSetUp>]
let Setup () =
    ()

let printTerm term =
    let str = sprintf "%A" term
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

let printState st =
    let code = getCode st
    let stk = getStack st
    let dump = getDump st
    let objs = List.zip stk (List.map (heapLookup (getHeap st)) stk)
    let str = sprintf " code:%A\n dump:%A\n stk:%A\n heap:%A\n*********" code dump stk objs
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

[<Test>]
let compileScKTest () =
    let code = compileSc ("K1", ["x"; "y"], (EVar "x"))
    Assert.AreEqual( ("K1", 2, [Push 0; Eval; Update 2; Pop 2; Unwind]), code );

[<Test>]
let compileScFTest () =
    let code = compileSc ("F", ["x"; "y"], (EAp (EVar "z", EVar "x")))
    Assert.AreEqual( ("F", 2, [Push 0; Pushglobal "z"; Mkap; Eval; Update 2; Pop 2; Unwind]), code );

[<Test>]
let compileProgTest () =
    let coreProg =
        [ ("main", [], (EAp (EVar "Z", EVar "y")));
          ("y", [], (ENum 1));
          ("Z", ["x"], (EVar "x")) ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    Assert.AreEqual( NNum 1, getResult finalSt )

[<Test>]
let testK () =
    let coreProg = [
        // K x y = x
        ("K", ["x"; "y"], EVar "x");
        // main = K 3 4
        ("main", [], EAp (EAp (EVar "K", ENum 3), ENum 4))
    ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    Assert.AreEqual( NNum 3, getResult finalSt )

[<Test>]
let testSKK3 () =
    let coreProg = [
        // K x y = x
        ("K", ["x"; "y"], EVar "x");
        // S f g x = f x (g x)
        ("S", ["f"; "g"; "x"], EAp (EAp (EVar "f", EVar "x"), EAp (EVar "g", EVar "x")));
        // main = S K K 3
        ("main", [], EAp (EAp (EAp (EVar "S", EVar "K"), EVar "K"), ENum 3))
    ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    Assert.AreEqual( NNum 3, getResult finalSt )

[<Test>]
[<Ignore("partial application case")>]
let testTwiceTwice () =
    let coreProg = [
        // twice f x = f (f x)
        ("twice", ["f"; "x"], EAp (EVar "f", EAp (EVar "f", EVar "x")))
        // id x = x
        ("id", ["x"], EVar "x");
         // main = twice twice id 3
        ("main", [], EAp (EVar "twice", EAp (EVar "twice", EAp (EVar "id", ENum 3))))
    ]
    let initSt = compile coreProg
    let rec repeat f n st =
        if n = 0 then st else repeat f (n-1) (f st)
    // List.map printState (List.map (fun n -> repeat step n initSt) [0..20])
    // Assert.Fail()
    let finalSt = List.last (eval initSt)
    Assert.AreEqual(NNum 3, getResult finalSt)

[<Test>]
[<Ignore("skip for now")>]
let testCompileArgs0 () =
    let defs = []
    let env = []
    let r = compileArgs defs env
    Assert.AreEqual([], r)

[<Test>]
let testCompileArgs1 () =
    let defs = [("x", ENum 1)]
    let env = []
    let r = compileArgs defs env
    Assert.AreEqual([(0, "x")], r)

[<Test>]
let testCompileArgs2 () =
    let defs = [("x", ENum 1); ("y", EVar "x")]
    let env = []
    let r = compileArgs defs env
    Assert.AreEqual([(1, "x"); (0, "y")], r)

[<Test>]
let testCompileArgs3 () =
    let defs = [("x", ENum 1); ("y", EVar "x")]
    let env = [(5, "z"); (6, "w")]
    let r = compileArgs defs env
    Assert.AreEqual([(1, "x"); (0, "y"); (7, "z"); (8, "w")], r)

[<Test>]
let testLet1 () =
    let coreProg = [
        ("main", [], ELet (false, [("t", ENum 3)], (EVar "t")))
    ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    Assert.AreEqual(NNum 3, getResult finalSt)

[<Test>]
let testLet2 () =
    let coreProg = [
        ("main", [], ELet (false, [("k", ENum 3); ("t", ENum 4)], EVar "t"))
    ]
    let initSt = compile coreProg
    try
        let finalSt = List.last (eval initSt)
        Assert.AreEqual(NNum 4, getResult finalSt)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testLetRecYCombinator () =
    let code = compileSc ("Y", ["f"], ELet (true, [("x", EAp (EVar "f", EVar "x"))], EVar "x"))
    Assert.AreEqual( ("Y", 1, [Alloc 1; Push 0; Push 2; Mkap; Update 0;
                               Push 0; Eval; Slide 1; Update 1; Pop 1; Unwind]), code )
[<Test>]
let testCompile1 () =
    let code = compileSc ("X", ["v"; "w"], EAp (EVar "v", EVar "w"))
    // env = [(0, "v"); (1, "w")]
    Assert.AreEqual ( ("X", 2, [Push 1; Push 1; Mkap; Eval;
                                Update 2; Pop 2; Unwind]), code )

[<Test>]
let testEval1 () =
    let heap = Map [(0, NNum 1)]
    let stk = [0]
    let dump = []
    let code = [Eval]
    let globals = Map [("0", 0)]
    let stats = 0
    let final = List.last (eval (code, stk, dump, heap, globals, stats))
    Assert.AreEqual (NNum 1, getResult final)

[<Test>]
let testEval2 () =
    let heap = Map [(0, NNum 0);
                    (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]))
                    (2, NAp (1, 0))
                   ]
    let stk = [2]
    let dump = []
    let code = [Eval]
    let globals = Map [("0", 0); ("f", 1)]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, NNum 0);
                         (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]));
                         (2, NInd 0)]
        let stk2 = [0]
        Assert.AreEqual (NNum 0, getResult final)
        Assert.AreEqual (heap2, getHeap final)
        Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testEval3 () =
    let heap = Map [(0, NNum 0);
                    (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]))
                    (2, NAp (1, 0))
                   ]
    let stk = [2; 2]
    let dump = []
    let code = [Eval]
    let globals = Map [("0", 0); ("f", 1)]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, NNum 0);
                         (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]));
                         (2, NInd 0)]
        let stk2 = [0]
        Assert.AreEqual (NNum 0, getResult final)
        Assert.AreEqual (heap2, getHeap final)
        // Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testEval4 () =
    let heap = Map [(0, NGlobal (0, [Pushint 3; Pushint 2; Push 0;
                                     Slide 2; Update 0; Pop 0; Unwind]))]
    let stk = []
    let dump = []
    let code = [Pushglobal "X"; Eval]
    let globals = Map [("X", 0)]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        Assert.AreEqual (NNum 2, getResult (List.last trace))
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testAlloc1 () =
    let heap = Map []
    let globals = Map []
    let stk = []
    let dump = []
    let code = [Alloc 2]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, hNull); (1, hNull)]
        let stk2 = [1; 0]
        Assert.AreEqual (heap2, getHeap final)
        Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testAlloc2 () =
    let heap = Map []
    let globals = Map []
    let stk = [3]
    let dump = []
    let code = [Alloc 2]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, hNull); (1, hNull)]
        let stk2 = [1; 0; 3]
        Assert.AreEqual (heap2, getHeap final)
        Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testCompile2 () =
    let code = compileSc ("X", [], ELet (false, [("k", ENum 3); ("t", ENum 2)], EVar "t"))
    // env = [(0, "k"); (1, "t")]
    Assert.AreEqual ( ("X", 0, [Pushint 3; Pushint 2; Push 0; Eval; Slide 2; Update 0; Pop 0; Unwind]), code )
    // @3 @2 @2

[<Test>]
[<Ignore("for output")>]
let testCompileLetRec1 () =
    let coreProg = [
        ("main", [], ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t"))
    ]
    let initSt = compile coreProg
    Assert.Ignore()

[<Test>]
[<Ignore("for output")>]
let testCompileSCLetRec1 () =
    let coreProg =
        ("main", [], ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t"))
   // printTerm (compileSc coreProg)
    Assert.Ignore()

[<Test>]
let testEvalLetRec1 () =
    let coreProg = [
        ("main", [], ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t"))
    ]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 3, res );

[<Test>]
let testEvalAdd1 () =
    let coreProg =
        [("main", [], EAdd (ENum 3, ENum 7))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );

[<Test>]
let testEvalMul1 () =
    let coreProg =
        [("main", [], EMul (EAdd (ENum 3, ENum 7), ENum 0))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 0, res );

[<Test>]
let testEvalEq () =
    let coreProg =
        [("main", [], EEq (ENum 7, ENum 3))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

[<Test>]
let testIfTrue () =
    let coreProg =
        [("main", [], EIf (ENum 1, ENum 10, ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );

[<Test>]
let testIfFalse () =
    let coreProg =
        [("main", [], EIf (ENum 0, ENum 10, ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 20, res );

[<Test>]
let testSub () =
    let coreProg =
        [("main", [], ESub (ENum 10, ENum 1))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 9, res );

[<Test>]
let testEqFalse () =
    let coreProg =
        [("main", [], EEq (ENum 10, ENum 1))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

let testEqTrue () =
    let coreProg =
        [("main", [], EEq (ENum 10, ENum 10))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NTrue, res );

[<Test>]
let testMul () =
    let coreProg =
        [("main", [], EMul (ENum 10, ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 200, res );

[<Test>]
let testGtTrue () =
    let coreProg =
        [("main", [], EGt (ENum 10, ENum 1))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NTrue, res );

[<Test>]
let testGtFalse () =
    let coreProg =
        [("main", [], EGt (ENum 1, ENum 10))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

[<Test>]
let testRec1 () =
    let coreProg =
        [("rec", ["n"], EIf (EGt (EVar "n", ENum 1), EAp (EVar "rec", ESub (EVar "n", ENum 1)), ENum 20))
         ("main", [], EAp (EVar "rec", ENum 10))]
    try
      let initSt = compile coreProg
      let finalSt = List.last (eval initSt)
      let res = getResult finalSt
      Assert.AreEqual( NNum 20, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testRec2 () =
    let coreProg =
        // rec n m = if (n > 1) then (rec (n-1) n) else m
        // rec 10 3 = rec 9 10  = rec 8 9 = rec 7 8 = rec 6 7 = ...
        //  ... = rec 1 2 = 2
        [("rec", ["n"; "m"],
          EIf (
            EGt (EVar "n", ENum 1),
            EAp (EAp (EVar "rec", ESub (EVar "n", ENum 1)), EVar "n"),
            EVar "m"
            )
          )
         ("main", [], EAp (EAp (EVar "rec", ENum 10), ENum 3))]
    try
      let initSt = compile coreProg
      // printTerm initSt
      let finalSt = List.last (eval initSt)
      let res = getResult finalSt
      Assert.AreEqual( NNum 2, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testSumRec () =
    let coreProg =
        // sum n acc = if (n > 0) then (sum (n-1) (acc+n)) else acc
        // sum 4 0 = sum 3 4 = sum 2 7 = sum 1 9 = sum 0 10 = 10
        [("sum", ["n"; "acc"],
          EIf (
            EGt (EVar "n", ENum 0),
            EAp (EAp (EVar "sum", ESub (EVar "n", ENum 1)), EAdd(EVar "acc", EVar "n")),
            EVar "acc"
            )
          );
         ("main", [], EAp (EAp (EVar "sum", ENum 4), ENum 0))
         ]
    try
      let initSt = compile coreProg
      // List.map printTerm (eval initSt) |> ignore
      let finalSt = List.last (eval initSt)
      let res = getResult finalSt
      // printTerm (getStats finalSt)
      Assert.AreEqual( NNum 10, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testMaxFunction () =
    let coreProg =
        [("max", ["n"; "m"], EIf (EGt (EVar "n", EVar "m"), EVar "n", EVar "m"));
         ("main", [], EAp (EAp (EVar "max", ENum 5), ENum 6))]
    try
      let initSt = compile coreProg
      let res = getResult (List.last (eval initSt))
      Assert.AreEqual( NNum 6, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testFact () =
    let coreProg =
        // fact n = if n == 0 then 1 else n * fact(n-1)
        // main = fact 5
        [("fact", ["n"],
          EIf (EEq (EVar "n", ENum 0),
               ENum 1, // true branch
               EMul (EVar "n", EAp (EVar "fact", ESub (EVar "n", ENum 1)))) // else branch
          )
         ("main", [], EAp (EVar "fact", ENum 5))]
    try
      let initSt = compile coreProg
      // List.map printTerm (eval initSt) |> ignore
      let res = getResult (List.last (eval initSt))
      Assert.AreEqual( NNum 120, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testConstr0 () =
    let coreProg =
        [("main", [], EPack (0, 0, []))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    Assert.AreEqual( NConstr (0, []), res );

[<Test>]
let testConstr1 () =
    let coreProg =
        [("main", [], EPack (0, 2, [ENum 1; ENum 2]))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (0, [2; 1]), res );
    Assert.AreEqual( heapLookup heap 2, NNum 1 );
    Assert.AreEqual( heapLookup heap 1, NNum 2 );

[<Test>]
let testConstr2 () =
    let coreProg =
        [("main", [], EPack (0, 2, [EAdd (ENum 1, ENum 2); ESub (ENum 10, ENum 5)]))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (0, [6; 3]), res );
    Assert.AreEqual( heapLookup heap 6, NNum 3 );
    Assert.AreEqual( heapLookup heap 3, NNum 5 );

[<Test>]
let testConstr3 () =
    // nested constructors
    let coreProg =
        [("main", [], EPack (0, 1, [EPack (1, 0, [])]))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (0, [1]), res );
    Assert.AreEqual( heapLookup heap 1, NConstr (1, []) );

[<Test>]
let testCase1 () =
    // nested constructors
    let coreProg =
        [("some", [], EPack (0, 1, [EPack (1, 0, [])]));
         ("main", [], ECase (EVar "some", [(0, ["x"], EVar "x")]))
         ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (1, []), res );

[<Test>]
let testCase2 () =
    // nested constructors
    let coreProg =
        [("some", [], EPack (1, 2, [ENum 1; ENum 2]));
         ("main", [], ECase (EVar "some", [(0, ["x"], EVar "x");
                                           (1, ["x"; "y"], EAdd (EVar "x", EVar "y"))
                                           ]
                             )
          )
         ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NNum 3, res );

[<Test>]
[<Ignore("bug")>]
let testLazyDiv0 () =
    let coreProg =
        [("main", [], EAp (EAp (EVar "K", ENum 1), EDiv(ENum 1, ENum 0)))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );

[<Test>]
let testUnwindInd0 () =
    let heap = Map []
    let stk = []
    let dump = []
    let globals = Map []
    let stats = 0
    let code = [Pushint 100; Pushint 200; Update 0; DumpStk; Unwind]
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        Assert.AreEqual (NNum 200, getResult (List.last trace))
        Assert.AreEqual ([1; 0], getStack (List.last trace))
    with
        | GMError s ->
            Assert.Fail(s)
