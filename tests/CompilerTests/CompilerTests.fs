module CompilerTests

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework

open System
open System.Collections.Generic
open Compiler
open type TVM.Value

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let testPushInt0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 1; Int 0], getResultStack final)

[<Test>]
let testAdd0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Add;
                             GMachine.Pushint 300;
                             GMachine.Add;
                             GMachine.Pushint 400;
                             GMachine.Add])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testAdd0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 6], getResultStack final) // 2 is a result address, not value
    Assert.AreEqual(nnum 1000, getResultHeap final)

[<Test>]
let testPushglobal0 () =
    let globals = Map [("add", 1)]
    let c7 = prepareC7 (prepareHeap (Map [])) (Int -1) (prepareGlobals globals) Null Null
    let code = compileCode [GMachine.Pushglobal "add"]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 1], getResultStack final)

[<Test>]
let testPushglobal1 () =
    let globals = Map [("fact", 1); ("main", 0)]
    let c7 = prepareC7 (prepareHeap (Map [])) (Int -1) (prepareGlobals globals) Null Null
    let code = compileCode [GMachine.Pushglobal "fib"]
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
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Add;
                             GMachine.Pushint 300;
                             GMachine.Mul;
                             GMachine.Pushint 500;
                             GMachine.Div]) // 500 / 900
    let st = TVM.initialState code
    TVM.dumpFiftScript "testMixedArith0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testEqual0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Equal])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testEqual0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testEqual1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Equal])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testEqual1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum -1, getResultHeap final)

[<Test>]
let testGreater0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 200;
                             GMachine.Pushint 100;
                             GMachine.Greater]) // 100 > 200 , GMachine has a different argument order
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testGreater1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Greater])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testGreater2 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Greater]) // 200 > 100
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater2.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum -1, getResultHeap final)

[<Test>]
let testDiv0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 50;
                             GMachine.Div]) // 50 / 100
    let st = TVM.initialState code
    TVM.dumpFiftScript "testDiv0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 0, getResultHeap final)

[<Test>]
let testDiv1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 50;
                             GMachine.Pushint 100;
                             GMachine.Div]) // 100 / 50
    let st = TVM.initialState code
    TVM.dumpFiftScript "testDiv1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 2, getResultHeap final)

[<Test>]
let testSub0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 50;
                             GMachine.Pushint 100;
                             GMachine.Sub]) // 100 - 50
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSub0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 50, getResultHeap final)

[<Test>]
let testSub1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint -50;
                             GMachine.Pushint 50;
                             GMachine.Sub]) // 50 - (-50)
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSub1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 100, getResultHeap final)

[<Test>]
let testmkAp () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Mkap])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int (int GMachine.NodeTags.NAp); Int 1; Int 0], getResultHeap final)
    Assert.AreEqual(nnum 100, getHeapAt 0 final)
    Assert.AreEqual(nnum 200, getHeapAt 1 final)

[<Test>]
let testUpdate0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100; // 0 (pos:2)
                             GMachine.Pushint 200; // 1 (pos:1)
                             GMachine.Pushint 300; // 2 (pos:0)
                             GMachine.Update 1])  // heap[0] = NInd 2, heap[2] = NNum 300
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUpdate0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final) // two int addresses on the stack
    Assert.AreEqual (Tup [Int (int GMachine.NodeTags.NInd); Int 2], getHeapAt 0 final)
    Assert.AreEqual (nnum 300, getHeapAt 2 final)

[<Test>]
let testUpdate1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100; // 0
                             GMachine.Pushint 300; // 1
                             GMachine.Update 0])  // heap[0] = NInd 1
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUpdate1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 0], getResultStack final) // 0 is an address of the 1st integer (100)
    Assert.AreEqual (nind 1, getHeapAt 0 final)
    Assert.AreEqual (nnum 300, getHeapAt 1 final)

[<Test>]
let testAlloc0 () =
    let code = initC7 @
               (compileCode [GMachine.Alloc 3])
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
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (30, 2)])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testPack0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nconstr 30 [1; 0], getResultHeap final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

[<Test>]
let testPack1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (30, 2);
                             GMachine.Pack (40, 1)]) // nested constructor
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
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (30, 2);
                             GMachine.Split 2])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSplit0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

[<Test>]
let testSplit1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (30, 2);
                             GMachine.Pack (40, 1);
                             GMachine.Split 1;
                             GMachine.Split 2])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testSplit1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

[<Test>]
let testCasejump0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (30, 2);
                             GMachine.Casejump [(0, [GMachine.Pushint 300]);
                                                (30, [GMachine.Pushint 600])]])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCasejump0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nnum 600, getResultHeap final)

[<Test>]
let testCasejump1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (30, 2);
                             GMachine.Casejump [(0, [GMachine.Pushint 300]);
                                                (20, [GMachine.Pushint 600])]])
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
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Equal;
                             GMachine.Cond ([GMachine.Pushint 300], [GMachine.Pushint 600])])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCond0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nnum 300, getResultHeap final)

[<Test>]
let testCond1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Equal;
                             GMachine.Cond ([GMachine.Pushint 300], [GMachine.Pushint 600])])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testCond1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual (nnum 600, getResultHeap final)

[<Test>]
let testUnwind0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwind0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getResultHeap final)

[<Test>]
let testGtTrueCompiler () =
    let coreProgGM =
        [("main", [], GMachine.EGt (GMachine.ENum 10, GMachine.ENum 1))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    let NTrue = nnum -1
    Assert.AreEqual (NTrue, getResultHeap final)

[<Test>]
let testSlide0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pushint 300;
                             GMachine.Slide 2])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 2], getResultStack final)

[<Test>]
let testSlide1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pushint 300;
                             GMachine.Slide 1])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 2; Int 0], getResultStack final)

[<Test>]
let testSlide2 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pushint 300;
                             GMachine.Slide 0])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 2; Int 1; Int 0], getResultStack final)

[<Test>]
let testPush0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Push 0])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 1; Int 1; Int 0], getResultStack final)

[<Test>]
let testPop0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Push 0;
                             GMachine.Pop 3])
    let st = TVM.initialState code
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([] :> TVM.Stack, getResultStack final)

[<Test>]
let testUnwindNGlobal () =
    let globals = prepareGlobals (Map [("add", 66)])
    let addGlobal = GMachine.NGlobal (0, [GMachine.Pushint 100; // @add 0
                                          GMachine.Pushint 200; // @add 0 1
                                          GMachine.Update 1; // @add 0
                                          GMachine.Pop 1; // @add
                                          GMachine.Unwind])
    let heap = prepareHeap (Map [(66, addGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont unwindSelectorCell
    let code = compileCode [GMachine.Pushglobal "add";
                            GMachine.Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual([Int 1], getResultStack final)
    Assert.AreEqual(nnum 200, getResultHeap final)

[<Test>]
let testUnwindNAp0 () =
    let globals = prepareGlobals (Map [("inc", 66)])
    let incGlobal = GMachine.NGlobal (1, [GMachine.Pushint 1; // f @n @1
                                          GMachine.Add; // f @(n+1)
                                          GMachine.Update 0; // f'
                                          GMachine.Pop 0;
                                          GMachine.Unwind])
    let heap = prepareHeap (Map [(66, incGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont unwindSelectorCell
    let code = compileCode [GMachine.Pushint 10;
                            GMachine.Pushglobal "inc";
                            GMachine.Mkap;
                            GMachine.Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 500)
    Assert.AreEqual([Int 3], getResultStack final)
    Assert.AreEqual(nnum 11, getResultHeap final)

[<Test>]
let testUnwindNAp2 () =
    let globals = prepareGlobals (Map [("inc", 66)])
    let incGlobal = GMachine.NGlobal (1, [GMachine.Push 0; // f @n @n
                                          GMachine.Eval;   // f @n !@n
                                          GMachine.Pushint 1; // f @n !@n @1
                                          GMachine.Add;    // f @n @(!n+1)
                                          GMachine.Update 1; // f' @n
                                          GMachine.Pop 1;  // f'
                                          GMachine.Unwind])
    let heap = prepareHeap (Map [(66, incGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont unwindSelectorCell
    let code = compileCode [GMachine.Pushint 10;
                            GMachine.Pushglobal "inc";
                            GMachine.Mkap;
                            GMachine.Pushglobal "inc";
                            GMachine.Mkap;
                            GMachine.Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual(nnum 12, getResultHeap final)

[<Test>]
let testUnwindNAp3 () =
    let globals = prepareGlobals (Map [("add", 66)])
    let addGlobal = GMachine.NGlobal (2, [GMachine.Push 1; // f @x @y @x
                                          GMachine.Eval;   // f @x @y !x
                                          GMachine.Push 1; // f @x @y @!x @y
                                          GMachine.Eval;   // f @x @y @!x @!y
                                          GMachine.Add;    // f @x @y @(!x+!y)
                                          GMachine.Update 2; // f' @x @y
                                          GMachine.Pop 2;  // f'
                                          GMachine.Unwind])
    let heap = prepareHeap (Map [(66, addGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont unwindSelectorCell
    let code = compileCode [GMachine.Pushint 10;
                            GMachine.Pushint 20;
                            GMachine.Pushglobal "add";
                            GMachine.Mkap;
                            GMachine.Mkap;
                            GMachine.Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual(nnum 30, getResultHeap final)

[<Test>]
let testUnwindNAp4 () =
    let globals = prepareGlobals (Map [("inc", 66); ("dec", 67); ("mix", 68)])
    let incGlobal =
        GMachine.NGlobal (1, [GMachine.Push 0;    // @f @x @x
                              GMachine.Eval;      // @f @x @!x
                              GMachine.Pushint 1; // @f @x @!x 10
                              GMachine.Add;       // @f @x @(!x+1)
                              GMachine.Update 1;  // @f' @x
                              GMachine.Pop 1;     // @f'
                              GMachine.Unwind])
    let decGlobal =
        GMachine.NGlobal (1, [GMachine.Pushint 1; // @f @x 1
                              GMachine.Push 1;    // @f @x 1 @x
                              GMachine.Eval;      // @f @x 1 @!x
                              GMachine.Sub;       // @f @x @(!x-1)
                              GMachine.Update 1;  // @f' @x
                              GMachine.Pop 1;     // @f'
                              GMachine.Unwind])
    let mixGlobal =
        GMachine.NGlobal (1, [GMachine.Push 0;             // @f @x @x
                              GMachine.Eval;
                              GMachine.Pushglobal "inc";   // @f @x @x @inc
                              GMachine.Mkap;               // @f @x @(ap @inc @x)
                              GMachine.Eval;               // @f @x @!(inc x)
                              GMachine.Pushglobal "dec";   // @f @x @!(inc x) @dec
                              GMachine.Mkap;               // @f @x @(ap @dec @!(inc x))
                              GMachine.Eval;               // @f @x @!ap
                              GMachine.Update 1;           // @f' @x
                              GMachine.Pop 1;              // @f'
                              GMachine.Unwind])

    let heap = prepareHeap (Map [(66, incGlobal); (67, decGlobal); (68, mixGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont unwindSelectorCell
    let code = compileCode [GMachine.Pushint 10;
                            GMachine.Pushglobal "mix";
                            GMachine.Mkap;
                            GMachine.Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 1000)
    Assert.AreEqual(nnum 10, getResultHeap final)

// NOTE: recursive function is used!
[<Test>]
let testUnwindNAp5 () =
    let globals = prepareGlobals (Map [("inc", 66); ("func", 68)])
    let incGlobal =
        GMachine.NGlobal (1, [GMachine.Push 0;    // @f @x @x
                              GMachine.Eval;      // @f @x @!x
                              GMachine.Pushint 1; // @f @x @!x 10
                              GMachine.Add;       // @f @x @(!x+1)
                              GMachine.Update 1;  // @f' @x
                              GMachine.Pop 1;     // @f'
                              GMachine.Unwind])
    // func x = if x < 10 then func (inc x) else x
    let funcGlobal =
        GMachine.NGlobal (1, [GMachine.Pushint 10; // @f @x @10
                              GMachine.Push 1;     // @f @x @10 @x
                              GMachine.Eval;       // @f @x @10 @!x
                              GMachine.Less;       // @f @x @(!x < 10?)
                              GMachine.Cond ([GMachine.Push 0; // @f @x @x
                                              GMachine.Eval;   // @f @x @!x
                                              GMachine.Pushglobal "inc";   // @f @x @!x @inc
                                              GMachine.Mkap;               // @f @x @(ap @inc @x)
                                              GMachine.Eval;               // @f @x @!(inc x)
                                              GMachine.Pushglobal "func";  // @f @x @!(inc x) @func
                                              GMachine.Mkap;               // @f @x @(ap @func @!(inc x))
                                              GMachine.Eval],               // @f @x @!ap
                                             [GMachine.Push 0])
                              GMachine.Update 1;   // @f' @x
                              GMachine.Pop 1;      // @f'
                              GMachine.Unwind])
    let heap = prepareHeap (Map [(66, incGlobal); (68, funcGlobal)])
    let c7 = prepareC7 heap (Int -1) globals unwindCont unwindSelectorCell
    let code = compileCode [GMachine.Pushint 5;
                            GMachine.Pushglobal "func";
                            GMachine.Mkap;
                            GMachine.Eval]
    let st = TVM.initialState code
    st.put_c7 c7
    let final = List.last (TVM.runVMLimits st false 5000)
    Assert.AreEqual(nnum 10, getResultHeap final)

[<Test>]
let testUnwindNConstr0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Pack (1,2);
                             GMachine.Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwindNConstr0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 2], getResultStack final)
    Assert.AreEqual (nconstr 1 [1; 0], getResultHeap final)

[<Test>]
let testUnwindNInd0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100; // 0     heap = [(0, Int 100)]
                             GMachine.Pushint 200; // 0 1   heap = [(0, Int 100), (1, Int 200)]
                             GMachine.Update 0; // 0        heap = [(0, NInd 1), (1, Int 200)]
                             GMachine.Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwindNInd0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1], getResultStack final)
    Assert.AreEqual (nnum 200, getResultHeap final)

[<Test>]
let testCompileConstr2 () =
    let coreProgGM =
        [("main", [], GMachine.EPack (0, 2, [GMachine.EAdd (GMachine.ENum 1, GMachine.ENum 2);
                                             GMachine.ESub (GMachine.ENum 10, GMachine.ENum 5)]))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt false 1000)
    match (getResultHeap final) with
        | Tup [Int 4; Int 0; Tup [x; y]] ->
           Assert.AreEqual (nnum 3, getHeapAt x.unboxInt final)
           Assert.AreEqual (nnum 5, getHeapAt y.unboxInt final)
        | _ ->
            Assert.Fail("heap object is not a constructor")

[<Test>]
let testCompileConstr3 () =
    let coreProgGM =
        [("main", [], GMachine.EPack (0, 1, [GMachine.EPack (1, 0, [])]))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    let final = List.last (TVM.runVMLimits tvmInitSt true 1000)
    match (getResultHeap final) with
        | Tup [Int 4; Int 0; Tup [Int 2]] ->
           match (getHeapAt 2 final) with
               | Tup [Int 4; Int 1; Tup []] ->
                    Assert.Pass()
               | _ as other ->
                    printfn "%A" other
                    printfn "%A" (tvmHeap final)
                    Assert.Fail("incorrect heap object")
        | _ as other ->
               printfn "%A" other
               Assert.Fail("incorrect heap object")
