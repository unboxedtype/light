// For emacs: -*- fsharp -*-
module Compiler2Tests

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework

open System
open System.Collections.Generic
open Compiler2
open type TVM.Value

open type GMachine.Expr
open type GMachine.Instruction
open type GMachine.Node

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let testPushInt0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 1; Int 0], getResultStack final)

[<Test>]
let testAdd0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Add;
                             Pushint 300;
                             Add;
                             Pushint 400;
                             Add])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testAdd0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 6], getResultStack final) // 2 is a result address, not value
    Assert.AreEqual(nnum 1000, getResultHeap final)

[<Test>]
let testPushglobal0 () =
    let globals = Map [("add", 1)]
    let c7 = prepareC7 (prepareHeap (Map [])) (Int -1) (prepareGlobals globals) Null
    let code = compileCode [Pushglobal "add"]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 1], getResultStack final)

[<Test>]
[<Ignore("The exception mechanism was changed")>]
let testPushglobal1 () =
    let globals = Map [("fact", 1); ("main", 0)]
    let c7 = prepareC7 (prepareHeap (Map [])) (Int -1) (prepareGlobals globals) Null
    let code = compileCode [Pushglobal "fib"]
    let st = TVM.initialState code
    st.put_c7 c7
    try
        let final = List.last (TVM.runVM st false)
        Assert.Fail("unreachable")
    with
        | TVM.TVMError(x) ->
            if x = string (int RuntimeErrors.GlobalNotFound) then
                Assert.Pass()
            else
                Assert.Fail("wrong exception")

[<Test>]
let testMixedArith0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Add;
                             Pushint 300;
                             Mul;
                             Pushint 500;
                             Div]) // 500 / 900
    let st = TVM.initialState code
    TVM.dumpFiftScript "testMixedArith0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testEqual0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Equal])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testEqual0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testEqual1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 100;
                             Equal])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testEqual1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum -1, getResultHeap final)

[<Test>]
let testGreater0 () =
    let code = initC7 @
               (compileCode [Pushint 200;
                             Pushint 100;
                             Greater]) // 100 > 200 , GMachine has a different argument order
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testGreater1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 100;
                             Greater])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testGreater2 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Greater]) // 200 > 100
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater2.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum -1, getResultHeap final)

[<Test>]
let testDiv0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 50;
                             Div]) // 50 / 100
    let st = TVM.initialState code
    TVM.dumpFiftScript "testDiv0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testDiv1 () =
    let code = initC7 @
               (compileCode [Pushint 50;
                             Pushint 100;
                             Div]) // 100 / 50
    let st = TVM.initialState code
    TVM.dumpFiftScript "testDiv1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 2, getResultHeap final)

[<Test>]
let testSub0 () =
    let code = initC7 @
               (compileCode [Pushint 50;
                             Pushint 100;
                             Sub]) // 100 - 50
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSub0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 50, getResultHeap final)

[<Test>]
let testSub1 () =
    let code = initC7 @
               (compileCode [Pushint -50;
                             Pushint 50;
                             Sub]) // 50 - (-50)
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSub1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 100, getResultHeap final)

[<Test>]
let testmkAp () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Mkap])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nap 1 0, getResultHeap final)
    Assert.AreEqual(nnum 100, getHeapAt 0 final)
    Assert.AreEqual(nnum 200, getHeapAt 1 final)

[<Test>]
let testUpdate0 () =
    let code = initC7 @
               (compileCode [Pushint 100; // 0 (pos:2)
                             Pushint 200; // 1 (pos:1)
                             Pushint 300; // 2 (pos:0)
                             Update 1])  // heap[0] = NInd 2, heap[2] = NNum 300
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUpdate0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final) // two int addresses on the stack
    Assert.AreEqual (nind 2, getHeapAt 0 final)
    Assert.AreEqual (nnum 300, getHeapAt 2 final)

[<Test>]
let testUpdate1 () =
    let code = initC7 @
               (compileCode [Pushint 100; // 0
                             Pushint 300; // 1
                             Update 0])  // heap[0] = NInd 1
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUpdate1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 0], getResultStack final) // 0 is an address of the 1st integer (100)
    Assert.AreEqual (nind 1, getHeapAt 0 final)
    Assert.AreEqual (nnum 300, getHeapAt 1 final)

[<Test>]
let testAlloc0 () =
    let code = initC7 @
               (compileCode [Alloc 3])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testAlloc0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 2; Int 1; Int 0], getResultStack final)
    Assert.AreEqual (Null, getHeapAt 0 final)
    Assert.AreEqual (Null, getHeapAt 1 final)
    Assert.AreEqual (Null, getHeapAt 2 final)

[<Test>]
let testPack0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (30, 2)])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testPack0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nconstr 30 [1; 0], getResultHeap final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

[<Test>]
let testPack1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (30, 2);
                             Pack (40, 1)]) // nested constructor
    let st = TVM.initialState code
    TVM.dumpFiftScript "testPack1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nconstr 40 [2], getResultHeap final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)
    Assert.AreEqual (nconstr 30 [1; 0], getHeapAt 2 final)

[<Test>]
let testSplit0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (30, 2);
                             Split 2])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSplit0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

[<Test>]
let testSplit1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (30, 2);
                             Pack (40, 1);
                             Split 1;
                             Split 2])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSplit1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

[<Test>]
let testCasejump0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (30, 2);
                             Casejump [(0, [Pushint 300]);
                                                (30, [Pushint 600])]])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCasejump0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nnum 600, getResultHeap final)

[<Test>]
[<Ignore("step handle exceptions")>]
let testCasejump1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (30, 2);
                             Casejump [(0, [Pushint 300]);
                                                (20, [Pushint 600])]])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCasejump1.fif" (TVM.outputFift st)
    try
        let final = List.last (TVM.runVM st false)
        Assert.Fail ("case not found exception is expected")
    with
        | TVM.TVMError(x) ->
            if x = string (int RuntimeErrors.CaseNotFound) then
                Assert.Pass()
            else
                Assert.Fail("wrong exception")

[<Test>]
let testCond0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 100;
                             Equal;
                             Cond ([Pushint 300], [Pushint 600])])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCond0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nnum 300, getResultHeap final)

[<Test>]
let testCond1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Equal;
                             Cond ([Pushint 300], [Pushint 600])])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCond1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nnum 600, getResultHeap final)

[<Test>]
let testUnwind0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwind0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getResultHeap final)

[<Test>]
let testGtTrueCompiler () =
    let coreProgGM =
        [("main", [], EGt (ENum 10, ENum 1))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    let NTrue = nnum -1
    Assert.AreEqual (NTrue, getResultHeap final)

[<Test>]
let testSlide0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pushint 300;
                             Slide 2])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 2], getResultStack final)

[<Test>]
let testSlide1 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pushint 300;
                             Slide 1])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 2; Int 0], getResultStack final)

[<Test>]
let testSlide2 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pushint 300;
                             Slide 0])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 2; Int 1; Int 0], getResultStack final)

[<Test>]
let testPush0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 100;
                             Push 0])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 1; Int 1; Int 0], getResultStack final)

[<Test>]
let testPop0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 100;
                             Push 0;
                             Pop 3])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([] :> TVM.Stack, getResultStack final)

[<Test>]
[<Ignore("absolute")>]
let testUnwindNGlobal () =
    let globals = prepareGlobals (Map [("add", 66)])
    let addGlobal = NGlobal (0, [Pushint 100; // @add 0
                                          Pushint 200; // @add 0 1
                                          Update 1; // @add 0
                                          Pop 1; // @add
                                          Unwind])
    let heap = prepareHeap (Map [(66, addGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont
    let code = compileCode [Pushglobal "add";
                            Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual([Int 1], getResultStack final)
    Assert.AreEqual(nnum 200, getResultHeap final)

[<Test>]
[<Ignore("absolute")>]
let testUnwindNAp0 () =
    let globals = prepareGlobals (Map [("inc", 66)])
    let incGlobal = NGlobal (1, [Pushint 1; // f @n @1
                                          Add; // f @(n+1)
                                          Update 0; // f'
                                          Pop 0;
                                          Unwind])
    let heap = prepareHeap (Map [(66, incGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont
    let code = compileCode [Pushint 10;
                            Pushglobal "inc";
                            Mkap;
                            Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 500)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual([Int 3], getResultStack final)
    Assert.AreEqual(nnum 11, getResultHeap final)

[<Test>]
[<Ignore("absolute")>]
let testUnwindNAp2 () =
    let globals = prepareGlobals (Map [("inc", 66)])
    let incGlobal = NGlobal (1, [Push 0; // f @n @n
                                          Eval;   // f @n !@n
                                          Pushint 1; // f @n !@n @1
                                          Add;    // f @n @(!n+1)
                                          Update 1; // f' @n
                                          Pop 1;  // f'
                                          Unwind])
    let heap = prepareHeap (Map [(66, incGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont
    let code = compileCode [Pushint 10;
                            Pushglobal "inc";
                            Mkap;
                            Pushglobal "inc";
                            Mkap;
                            Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual(nnum 12, getResultHeap final)

[<Test>]
[<Ignore("absolute")>]
let testUnwindNAp3 () =
    let globals = prepareGlobals (Map [("add", 66)])
    let addGlobal = NGlobal (2, [Push 1; // f @x @y @x
                                          Eval;   // f @x @y !x
                                          Push 1; // f @x @y @!x @y
                                          Eval;   // f @x @y @!x @!y
                                          Add;    // f @x @y @(!x+!y)
                                          Update 2; // f' @x @y
                                          Pop 2;  // f'
                                          Unwind])
    let heap = prepareHeap (Map [(66, addGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont
    let code = compileCode [Pushint 10;
                            Pushint 20;
                            Pushglobal "add";
                            Mkap;
                            Mkap;
                            Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual(nnum 30, getResultHeap final)

[<Test>]
[<Ignore("absolute")>]
let testUnwindNAp4 () =
    let globals = prepareGlobals (Map [("inc", 66); ("dec", 67); ("mix", 68)])
    let incGlobal =
        NGlobal (1, [Push 0;    // @f @x @x
                              Eval;      // @f @x @!x
                              Pushint 1; // @f @x @!x 10
                              Add;       // @f @x @(!x+1)
                              Update 1;  // @f' @x
                              Pop 1;     // @f'
                              Unwind])
    let decGlobal =
        NGlobal (1, [Pushint 1; // @f @x 1
                              Push 1;    // @f @x 1 @x
                              Eval;      // @f @x 1 @!x
                              Sub;       // @f @x @(!x-1)
                              Update 1;  // @f' @x
                              Pop 1;     // @f'
                              Unwind])
    let mixGlobal =
        NGlobal (1, [Push 0;             // @f @x @x
                              Eval;
                              Pushglobal "inc";   // @f @x @x @inc
                              Mkap;               // @f @x @(ap @inc @x)
                              Eval;               // @f @x @!(inc x)
                              Pushglobal "dec";   // @f @x @!(inc x) @dec
                              Mkap;               // @f @x @(ap @dec @!(inc x))
                              Eval;               // @f @x @!ap
                              Update 1;           // @f' @x
                              Pop 1;              // @f'
                              Unwind])

    let heap = prepareHeap (Map [(66, incGlobal); (67, decGlobal); (68, mixGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont
    let code = compileCode [Pushint 10;
                            Pushglobal "mix";
                            Mkap;
                            Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 2000)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual(nnum 10, getResultHeap final)

// NOTE: recursive function is used!
[<Test>]
[<Ignore("the manual code")>]
let testUnwindNAp5 () =
    let globals = prepareGlobals (Map [("inc", 66); ("func", 68)])
    let incGlobal =
        NGlobal (1, [Push 0;    // @f @x @x
                              Eval;      // @f @x @!x
                              Pushint 1; // @f @x @!x 10
                              Add;       // @f @x @(!x+1)
                              Update 1;  // @f' @x
                              Pop 1;     // @f'
                              Unwind])
    // func x = if x < 10 then func (inc x) else x
    // This function is tail recursive, so the stack doesn't grow
    let funcGlobal =
        NGlobal (1, [Pushint 10; // @f @x @10
                              Push 1;     // @f @x @10 @x
                              Eval;       // @f @x @10 @!x
                              Less;       // @f @x @(!x < 10?)
                              Cond ([Push 0; // @f @x @x
                                     Eval;   // @f @x @!x
                                     Pushglobal "inc";   // @f @x @!x @inc
                                     Mkap;               // @f @x @(ap @inc @x)
                                     Eval;               // @f @x @!(inc x)
                                     Pushglobal "func";  // @f @x @!(inc x) @func
                                     Mkap;               // @f @x @(ap @func @!(inc x))
                                     Slide 2;            // @(ap ...)
                                     Eval],              // @!ap
                                    [Push 0]);
                              Update 1;   // @f' @x
                              Pop 1;      // @f'
                              Unwind])
    let heap = prepareHeap (Map [(66, incGlobal); (68, funcGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont
    let code = compileCode [Pushint 1;
                            Pushglobal "func";
                            Mkap;
                            Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 10000)
    Assert.AreEqual(nnum 10, getResultHeap final)
    Assert.AreEqual (1, List.length (getResultStack final));

[<Test>]
let testUnwindNConstr0 () =
    let code = initC7 @
               (compileCode [Pushint 100;
                             Pushint 200;
                             Pack (1,2);
                             Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwindNConstr0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual ([Int 2], getResultStack final)
    Assert.AreEqual (nconstr 1 [1; 0], getResultHeap final)

[<Test>]
let testUnwindNInd0 () =
    let code = initC7 @
               (compileCode [Pushint 100; // 0     heap = [(0, Int 100)]
                             Pushint 200; // 0 1   heap = [(0, Int 100), (1, Int 200)]
                             Update 0; // 0        heap = [(0, NInd 1), (1, Int 200)]
                             Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwindNInd0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (1, List.length (getResultStack final));
    Assert.AreEqual ([Int 1], getResultStack final)
    Assert.AreEqual (nnum 200, getResultHeap final)

[<Test>]
let testCompileConstr2 () =
    let coreProgGM =
        [("main", [], EPack (0, 2, [EAdd (ENum 1, ENum 2);
                                             ESub (ENum 10, ENum 5)]))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    Assert.AreEqual (1, List.length (getResultStack final));
    if debug then
        match (getResultHeap final) with
            | Tup [Int 4; _; Int 0; Tup [x; y]] ->
                Assert.AreEqual (nnum 3, getHeapAt x.unboxInt final)
                Assert.AreEqual (nnum 5, getHeapAt y.unboxInt final)
            | _ ->
                Assert.Fail("heap object is not a constructor")
    else
        match (getResultHeap final) with
            | Tup [_; Int 0; Tup [x; y]] ->
                Assert.AreEqual (nnum 3, getHeapAt x.unboxInt final)
                Assert.AreEqual (nnum 5, getHeapAt y.unboxInt final)
            | _ ->
                Assert.Fail("heap object is not a constructor")

[<Test>]
let testCompileConstr3 () =
    let coreProgGM =
        [("main", [], EPack (0, 1, [EPack (1, 0, [])]))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    Assert.AreEqual (1, List.length (getResultStack final));
    if debug then
        match (getResultHeap final) with
            | Tup [Int 4; _; Int 0; Tup [x]] ->
                match (getHeapAt x.unboxInt final) with
                    | Tup [Int 4; _; Int 1; Tup []] ->
                        Assert.Pass()
                    | _ as other ->
                        Assert.Fail("incorrect heap object")
            | _ as other ->
                Assert.Fail("incorrect heap object")
    else
        match (getResultHeap final) with
            | Tup [_; Int 0; Tup [x]] ->
                match (getHeapAt x.unboxInt final) with
                    | Tup [_; Int 1; Tup []] ->
                        Assert.Pass()
                    | _ as other ->
                        Assert.Fail("incorrect heap object")
            | _ as other ->
                Assert.Fail("incorrect heap object")

[<Test>]
let testCompileConstr4 () =
    let coreProgGM =
        let c1 = EPack (1, 0, []) // tag 1
        let c2 = EPack (2, 1, [c1]) // tag 2
        let c3 = EPack (3, 2, [c2; c1]) // tag 3
        let c4 = EPack (4, 3, [c3; c1; c2]) // tag 4
        [("main", [], c4)] // 0
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    if debug then
        match (getResultHeap final) with
            | Tup [Int 4; _; Int 4; Tup l4] ->
                let c3' = getHeapAt (List.item 0 l4).unboxInt final
                let c1' = getHeapAt (List.item 1 l4).unboxInt final
                let c2' = getHeapAt (List.item 2 l4).unboxInt final
                if ( (c3'.unboxTup.[0].unboxInt + c1'.unboxTup.[0].unboxInt + c2'.unboxTup.[0].unboxInt) = 4 * 3) &&
                    (c3'.unboxTup.[2].unboxInt = 3) && (c1'.unboxTup.[2].unboxInt = 1) && (c2'.unboxTup.[2].unboxInt = 2) then
                        Assert.Pass()
                else
                    Assert.Fail("incorrect heap object")
            | _ ->
                Assert.Fail("incorrect heap object")
    else
        Assert.Pass()

[<Test>]
let testCase1 () =
    let coreProgGM =
        [("some", [], EPack (0, 1, [EPack (1, 0, [])]));
         ("main", [], ECase (EVar "some", [(0, ["x"], EVar "x")]))
         ]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    if debug then
        match (getResultHeap final) with
            | Tup [Int 4; _; Int 1; Tup []] ->
                Assert.AreEqual (1, List.length (getResultStack final));
            | _ as other ->
                printfn "%A" other
                Assert.Fail("incorrect heap object")
    else
        match (getResultHeap final) with
            | Tup [_; Int 1; Tup []] ->
                Assert.AreEqual (1, List.length (getResultStack final));
            | _ as other ->
                Assert.Fail("incorrect heap object")

[<Test>]
let testCase2 () =
    let coreProgGM =
        [("some", [], EPack (1, 2, [ENum 1; ENum 2]));
         ("main", [], ECase (EVar "some",
                                      [(0, ["x"], EVar "x");
                                       (1, ["x"; "y"], EAdd (EVar "x", EVar "y"))])
          )
        ]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    Assert.AreEqual (nnum 3, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));

[<Test>]
let testChoice () =
    let coreProgGM =
        [("first", ["n"; "m"], EVar "n");
         ("second", ["n"; "m"], EVar "m");
         ("main", [], EAp (EAp (EVar "second", ENum 10), ENum 6))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 3000)
    Assert.AreEqual (nnum 6, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));

[<Test>]
let testIfThenElseTrue () =
    let coreProgGM =
        [("main", [], EIf (EGt (ENum 6, ENum 10), ENum 1, ENum 0))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testIfThenElseTrue.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 3000)
    Assert.AreEqual (nnum 0, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testIfThenElseFalse () =
    let coreProgGM =
        [("main", [], EIf (EGt (ENum 10, ENum 6), ENum 1, ENum 0))]
    let gmInitSt = GMachine.putCode [Pushglobal "main";
                                     Eval] (GMachine.compile coreProgGM)
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    Assert.AreEqual (nnum 1, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testMaxFunction0 () =
    let coreProgGM =
        [("max", ["n"], EIf (EGt (EVar "n", ENum 5), EVar "n", ENum 5));
         ("main", [], EAp (EVar "max", ENum 10))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    Assert.AreEqual (nnum 10, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testMaxFunction1 () =
    let coreProgGM =
        [("max", ["n"; "m"], EIf (EGt (EVar "n", EVar "m"), EVar "n", EVar "m"));
         ("main", [], EAp (EAp (EVar "max", ENum 10), ENum 6))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    Assert.AreEqual (nnum 10, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testFactorial5 () =
    // fact n = if n == 0 then 1 else n * fact(n-1)
    // main = fact 5
    let coreProgGM =
        [("fact", ["n"],
          EIf (
            EEq (EVar "n", ENum 0),
            ENum 1, // true branch
            EMul (EVar "n",
                           EAp (EVar "fact",
                                         ESub (EVar "n",
                                                        ENum 1)))) // else branch
          )
         ("main", [], EAp (EVar "fact", ENum 5))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testFactorial5.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 5000)
    Assert.AreEqual (nnum 120, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testFactorial10 () =
    // fact n = if n == 0 then 1 else n * fact(n-1)
    // main = fact 10
    let coreProgGM =
        [("fact", ["n"],
          EIf (
            EEq (EVar "n", ENum 0),
            ENum 1, // true branch
            EMul (EVar "n",
                           EAp (EVar "fact",
                                         ESub (EVar "n",
                                                        ENum 1)))) // else branch
          )
         ("main", [], EAp (EVar "fact", ENum 10))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testFactorial10.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 5000)
    Assert.AreEqual (nnum 3628800, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testCompiler2Factorial5 () =
    // fact n = if n == 0 then 1 else n * fact(n-1)
    // main = fact 5
    let coreProgGM =
        [("fact", ["n"],
          EIf (
            EIsZero (EVar "n"),
            ENum 1, // true branch
            EMul (EVar "n",
                           EAp (EVar "fact",
                                         EDec (EVar "n")))) // else branch
          )
         ("main", [], EAp (EVar "fact", ENum 5))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testCompiler2Factorial5.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 5000)
    Assert.AreEqual (nnum 120, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

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
    let coreProgGM =
        [("f", ["n"], EInc (EVar "n"));
         ("List.map", ["fun"; "l"],
          ECase (EVar "l",
                 [(1, [], ENum 0);
                  (2, ["h"; "t"],
                   ELet (false, [("h'", EAp (EVar "fun", EVar "h"));
                                 ("t'", EAp (EAp (EVar "List.map", EVar "fun"), EVar "t"))],
                         EAdd (EVar "h'", EVar "t'")))
                  ]
                 )
          );
         ("main", [], EAp (EAp (EVar "List.map", EVar "f"), myList))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testMapList.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 10000)
    // printfn "%A" (tvmInitSt.cr.c7.unboxTup.Item 3)
    // printfn "%A" (getResultStack final)
    // printfn "%A" (List.indexed (simplifyHeap (tvmHeap final)))
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testStubGas () =
    let coreProgGM =
        [("main", [], ENum 0)] // minimal program?
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testStubGas.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 3000)
    Assert.AreEqual (nnum 0, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testAddTwoNumbers () =
    let coreProgGM =
        [("main", [], EAdd (ENum 10, ENum 20))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testAddTwoNumbers.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 3000)
    Assert.AreEqual (nnum 30, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testAddThreeNumbers () =
    let coreProgGM =
        [("main", [], EAdd (ENum 30, EAdd (ENum 10, ENum 20)))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testAddThreeNumbers.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 3000)
    Assert.AreEqual (nnum 60, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)

[<Test>]
let testAddTenNumbers () =
    let rec addSeries l =
        match l with
            | [] -> ENum 0
            | [n] -> ENum n
            | h :: t -> EAdd (ENum h, addSeries t)
    let coreProgGM =
        [("main", [], addSeries [1..10])]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testAddTenNumbers.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVMLimits tvmInitSt false 3000)
    Assert.AreEqual (nnum 55, getResultHeap final);
    Assert.AreEqual (1, List.length (getResultStack final));
    printfn "%A: Gas consumed: %d"
            NUnit.Framework.TestContext.CurrentContext.Test.Name
            (final.gas.gas_limit - final.gas.gas_remaining)
