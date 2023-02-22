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
    Assert.Pass()

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
[<Ignore("globals are empty")>]
let testPushglobal0 () =
    let code = initC7 @ (mapPushglobal (hash "fact"))
    let st = TVM.initialState code
    // TVM.dumpFiftScript "testAdd0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 200], getResultStack final) // 2 is a result address, not value

[<Test>]
[<Ignore("globals are empty")>]
let testPushglobal1 () =
    let code = initC7 @ (mapPushglobal (hash "fibonacci"))
    let st = TVM.initialState code
    // TVM.dumpFiftScript "testAdd0.fif" (TVM.outputFift st)
    try
        let final = List.last (TVM.runVM st false)
        Assert.Fail ("global does not exist")
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
                             GMachine.Div])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testMixedArith0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum 180, getResultHeap final)

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
let testmkAp () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Mkap])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int (int GMachine.NodeTags.NAp); Int 0; Int 1], getResultHeap final)
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
    Assert.AreEqual (Tup [Int (int GMachine.NodeTags.NConstr); Int 30; Tup [Int 0; Int 1]], getResultHeap final)
    Assert.AreEqual (nnum 100, getHeapAt 0 final)
    Assert.AreEqual (nnum 200, getHeapAt 1 final)

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
let testUnwind1 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Mkap;
                             GMachine.Update 0;
                             GMachine.Pop 0;
                             GMachine.Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUnwind1.fif" (TVM.outputFift st)
    try
        let final = List.last (TVM.runVM st false)
        Assert.Fail("shall throw exception at this point");
    with
        | _ ->
            Assert.Pass()
[<Test>]
[<Ignore("not correct")>]
let testUpdatePop0 () =
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Update 0;
                             GMachine.Pop 0;
                             GMachine.Unwind])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUpdatePop0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 0], getResultStack final)
    Assert.AreEqual (nnum 100, getResultHeap final)

[<Test>]
let testGtTrueCompiler () =
    let coreProgGM =
        [("main", [], GMachine.EGt (GMachine.ENum 10, GMachine.ENum 1))]
    let gmInitSt = GMachine.compile coreProgGM
    let tvmInitSt = compile gmInitSt
    TVM.dumpFiftScript "testGtTrueCompiler.fif" (TVM.outputFift tvmInitSt)
    let final = List.last (TVM.runVM tvmInitSt false)
    let NTrue = nnum -1
    Assert.AreEqual (NTrue, getResultHeap final)