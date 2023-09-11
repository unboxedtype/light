// For emacs: -*- fsharp -*-

module TVMTests

open NUnit.Framework

// Incomplete pattern matches on this expression.
#nowarn "25"

open System
open System.Collections.Generic
open TVM


[<Test>]
let testInitState () =
    let st = initialState []
    Assert.AreEqual (st, step st false)

[<Test>]
let testPushInt0 () =
    let st = initialState [PushInt 10]
    let finalSt = List.last (runVM st false)
    Assert.AreEqual ( Some (Int 10), getResult finalSt )

[<Test>]
let testPushInt1 () =
    let st = initialState [PushInt 10; PushInt 20]
    let finalSt = List.last (runVM st false)
    Assert.AreEqual ( Some (Int 20), getResult finalSt )

[<Test>]
let testPush0 () =
    let st = initialState [PushInt 10; PushInt 20; Push 1]
    try
        let states = runVM st true
        let finalSt = List.last states
//        printTerm finalSt
        Assert.AreEqual ( Some (Int 10), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPush1 () =
    let st = initialState [PushInt 10; PushInt 20; Push 0]
    try
        let finalSt = List.last (runVM st false)
//        printTerm finalSt
        Assert.AreEqual ( Some (Int 20), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPop0 () =
    let st = initialState [PushInt 10; PushInt 20; Pop 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 10), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPop1 () =
    let st = initialState [PushInt 10; PushInt 20; Pop 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 20), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPop2 () =
    let st = initialState [PushInt 30; PushInt 10; PushInt 20; Pop 1; Pop 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 30), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testAdd () =
    let st = initialState [PushInt 30; PushInt 10; Add]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 40), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSub () =
    let st = initialState [PushInt 30; PushInt 10; Sub]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ( Some (Int 20), getResult finalSt )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute0 () =
    let st = initialState [PushCont []]
    let emptyCont = Cont emptyContinuation
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some emptyCont, getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute1 () =
    let st = initialState [PushCont []; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (None, getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute2 () =
    let st = initialState [PushCont [PushInt 10]; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute3 () =
    let st = initialState [PushInt 10; PushCont [PushInt 20; Add]; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 30), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecute4 () =
    let st = initialState [PushInt 10;
                           PushCont [PushCont [PushInt 20]; Execute; Add];
                           Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 30), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

let testExecute5 () =
    let st = initialState [PushCont [PushCont [PushInt 30]]; Execute; Execute; PushInt 20]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 20), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)


[<Test>]
let testIfElse0 () =
    let st = initialState [PushInt 0;
                           PushCont [PushInt 10];
                           PushCont [PushInt 20];
                           IfElse]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 20), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testXchg0 () =
    let st = initialState [PushInt 10; PushInt 20; Xchg 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testXchg1 () =
    let st = initialState [PushInt 30; PushInt 10; PushInt 20; Xchg 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 30), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testXchgId () =
    let st = initialState [PushInt 30; PushInt 10; PushInt 20; Xchg 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 20), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater0 () =
    let st = initialState [PushInt 30; PushInt 10; Greater]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int -1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater1 () =
    let st = initialState [PushInt 10; PushInt 30; Greater]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater2 () =
    // let f n = if n > 10 then n else (n - 1)
    let st = initialState [Push 0;
                           PushInt 10;
                           Greater;
                           PushCont [];
                           PushCont [PushInt 1; Sub];
                           IfElse]
    st.stack <- [Int 7]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 6), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testGreater3 () =
    // Recursion
    // let f n g =
    //    if n > 10 then (g (n - 1)) else n
    // eval (f 12 f)
    let st = initialState [PushCont [Push 1;    // n f n
                                     PushInt 0; // 0 n f n
                                     Greater; // (n > 0?) f n
                                     PushCont [Xchg 1; // n f
                                               PushInt 1; // 1 n f
                                               Sub;  // (n-1) f
                                               Xchg 1; // f (n-1)
                                               Push 0; // f f (n-1)
                                               Execute]; //
                                     PushCont [Push 1] // c2 c1 (n>0?) f n
                                     IfElse]; // f n
                           Push 0; // f f n
                           Execute // -> f n
                           ]
    st.stack <- [Int 12]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTuple0 () =
    let st = initialState [Nil]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTuple1 () =
    let st = initialState [Nil; Tuple 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Tup []]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTuple2 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 1; Int 2]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndex0 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2; Index 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndex1 () =
    let st = initialState [Nil; Index 0]
    try
        runVM st false |> ignore
    with
        | _ ->
            Assert.Pass()

[<Test>]
let testUntuple0 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2; Untuple 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 1), getResult finalSt)
    with
        | Failure s ->
            Assert.Fail(s)

[<Test>]
let testUntuple1 () =
    // exception is anticipated here
    let st = initialState [Nil; Untuple 2]
    try
        runVM st false |> ignore
    with
        | Failure s ->
            Assert.Pass()

[<Test>]
let testSetIndex0 () =
    let st = initialState [PushInt 1; PushInt 2; Tuple 2;
                           PushInt 3; SetIndex 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 3; Int 2]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testNewC () =
    let st = initialState [Newc]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Builder (CellData ([], [], 0u))), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testEndC () =
    let st = initialState [Newc; Endc]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Cell (CellData ([], [], 0u))), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testStu0 () =
    let st = initialState [PushInt 100; Newc; Sti 8]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Builder (CellData ([SInt (100, 8u)], [], 8u))), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testStu1 () =
    let st = initialState [PushInt 200;
                           PushInt 100;
                           Newc;
                           Sti 256;
                           Sti 256]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (
            Some (Builder (CellData ([SInt (100, 256u); SInt (200, 256u)], [], 512u))),
            getResult finalSt
        )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict0 () =
    let st = initialState [PushInt 10; // 10
                           Newc; // 10 b
                           Sti 128; // b'
                           PushInt 200; // b' 200(key)
                           NewDict; // b' 200 D
                           PushInt 10; // b' 200 D 10
                           DictISetB] // D'
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (
            Some (Cell (CellData ([SDict (Map [(200, [SInt (10, 128u)])])], [], 0u))),
            getResult finalSt
        )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDict1 () =
    let st = initialState [DictIGet] // k D' i -> v
    st.stack <- [Int 128;
                 Cell (CellData ([SDict (Map [(200, [SInt (10, 128u)])])], [], 0u)); Int 200]
    try
        let finalSt = List.last (runVM st false)
        let ((Int 0) :: (Int -1) :: s1 :: t) = finalSt.stack
        Assert.AreEqual (
            (Int 0) :: (Int -1) :: [Slice (CellData ([SInt (10, 128u)], [], 128u))],
            List.take 3 finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPushctr0 () =
    let st = initialState [PushCtr 7] // k D' i -> v
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPopctr0 () =
    let st = { TVMState.Default with code = [PushCtr 7; PushInt 200; TPush;
                                             PopCtr 7; PushCtr 7] }
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Tup [Int 200]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPopctr1 () =
    let st = initialState [PushCont [PushInt 10]; PopCtr 3; PushCtr 3; Execute]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testCalldict0 () =
    let st = initialState [PushCont [Drop; PushInt 10]; PopCtr 3; CallDict 5]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual (Some (Int 10), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev0 () =
    let st = initialState [RollRev 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ([Int 0], finalSt.stack) // success int
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev1 () =
    let st = initialState [PushInt 1; RollRev 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual ([Int 0; Int 1], finalSt.stack) // success int
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev2 () =
    let st = initialState [PushInt 1; RollRev 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("must not reach this point")
    with
        | _ ->
            Assert.Pass() // Stack underflow

[<Test>]
let testRollRev3 () =
    let st = initialState [PushInt 1; PushInt 2; RollRev 1]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 0; Int 1; Int 2], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev4 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; RollRev 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 0; Int 2; Int 1; Int 3], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRoll0 () =
    let st = initialState [Roll 0]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 0], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRoll1 () =
    let st = initialState [PushInt 1; PushInt 2; Roll 1]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 1; Int 2], stk)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRoll2 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; Roll 2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 1; Int 3; Int 2], stk)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRoll3 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; PushInt 4; Roll 2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 2; Int 4; Int 3; Int 1], stk)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev5 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; PushInt 4; RollRev 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 0; Int 3; Int 2; Int 4; Int 1], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRollRev6 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; PushInt 4; RollRev 3]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 0; Int 3; Int 2; Int 1; Int 4], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

// a0 : a1 : a2 : ... an : sn
// -->
// a1' : a2' : .. an' :  an : sn
// ai' = map ai
// k is just a recursive counter
let rec rearrange n map st =
    failIf (st.stack.Length <= n) "rearrange: stack underflow"
    let rec rearrange2 k n st =
        if k > n then st
        else
            rearrange2 (k + 1) n (drop (xchg (k + 1) (map k st)))
    let drop_a0 = drop st // remove the a0 element
    if n > 0 then
        let dup_an = rollrev (n-1) (push (n-1) drop_a0) // dup an element
        rearrange2 0 (n-1) dup_an
    else
        drop_a0

[<Test>]
let testRearrange0 () =
    let st = initialState []
    st.put_stack ([Int 1; Int 2; Int 3])
    try
        let finalSt = rearrange 2 (fun k -> push k) st
        Assert.AreEqual([Int 2; Int 3; Int 3], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange1 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    try
        let finalSt = rearrange 0 (fun k -> push k) st
        Assert.Fail("rearrange should work only with non-empty stack")
    with
        | _ ->
            Assert.Pass() // ok

[<Test>]
let testRearrange2 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    st.put_stack ([Int 1; Int 2])
    try
        let finalSt = rearrange 1 (fun k -> push k) st
        Assert.AreEqual([Int 2; Int 2], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange3 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    st.put_stack ([Int 1; Int 2; Int 3; Int 4])
    try
        let finalSt = rearrange 2 (fun k -> push k) st
        Assert.AreEqual([Int 2; Int 3; Int 3; Int 4], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRearrange4 () =
    // a0 : a1 : a2 : ... an : sn
    // -->
    // a1 : a2 : .. an :  an : sn
    let st = initialState []
    st.put_stack ([Int 1])
    try
        let finalSt = rearrange 1 (fun k -> push k) st
        Assert.Fail("stack underflow shall happen")
    with
        | Failure s ->
            Assert.Pass(s)

[<Test>]
let testRearrange6 () =
    let st = initialState []
    st.put_stack ([Int 1; Int 2; Int 3])
    try
        let finalSt = rearrange 0 (fun k -> push k) st
        Assert.AreEqual([Int 2; Int 3], finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTupleVar0 () =
    let st = initialState [PushInt 0; TupleVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTupleVar1 () =
    let st = initialState [PushInt 100; PushInt 1; TupleVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup [Int 100]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testTupleVar2 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2; TupleVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup [Int 200; Int 100]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDivmod0 () =
    let st = initialState [PushInt 10; PushInt 3; DivMod]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual([Int 1; Int 3], List.tail finalSt.stack)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndexvar0 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2;
                           TupleVar; PushInt 1; IndexVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 100), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIndexvar1 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2;
                           TupleVar; PushInt 3; IndexVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("range error")
    with
        | _ ->
            Assert.Pass()

[<Test>]
let testSetindexvar0 () =
    let st = initialState [PushInt 200; PushInt 100; PushInt 2;
                           TupleVar; PushInt 300; PushInt 1;
                           SetIndexVar]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup [Int 200; Int 300]), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRepeat0 () =
    let st = initialState [PushInt 0; PushCont [PushInt 200]; Repeat]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(None, getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRepeat1 () =
    let st = initialState [PushInt 1; PushCont [PushInt 100]; Repeat]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 100), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRepeat2 () =
    let st = initialState [PushInt 3; PushCont [Nil]; Repeat]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Tup []), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDepth0 () =
    let st = initialState [Depth]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDepth1 () =
    let st = initialState [PushInt 100; Depth]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDepth2 () =
    let st = initialState [PushInt 100; PushInt 200; Drop; Drop; Depth]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDec0 () =
    let st = initialState [PushInt 0; Dec]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int -1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testDec1 () =
    let st = initialState [PushCont []; Dec]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("Dec expects integer")
    with
        | _ -> Assert.Pass()

[<Test>]
let testPick0 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2; PushInt 2; Pick]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testPick1 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2; PushInt 3; Pick]
    try
        let finalSt = List.last (runVM st false)
        Assert.Fail("Out of bound")
    with
        | _ -> Assert.Pass()

[<Test>]
let testXchgx0 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2;
                           PushInt 1; XchgX]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testBlkDrop0 () =
    let st = initialState [PushInt 0; PushInt 1; PushInt 2; PushInt 3; BlkDrop 2]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIsNull0 () =
    let st = initialState [PushNull; IsNull]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int -1), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testIsNull1 () =
    let st = initialState [PushInt 0; IsNull]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSwap () =
    let st = initialState [PushInt 0; PushInt 1; Swap]
    try
        let finalSt = List.last (runVM st false)
        Assert.AreEqual(Some (Int 0), getResult finalSt)
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSwap2 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3; PushInt 4; Swap2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 2; Int 1; Int 4; Int 3], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testRot2 () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3;
                           PushInt 4; PushInt 5; PushInt 6; Rot2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 2; Int 1; Int 6; Int 5; Int 4; Int 3], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecutePushCtr0 () =
    // this is unintuitive; The continuation in C0 already has save.c0 set,
    // so the obvious return point to PushInt 2 will be changed back to
    // that save.c0, which is contQuit. So, this code will execute only one
    // PushInt 1.
    let st = initialState [PushCont [PushCtr 0; Execute; PushInt 2]; Execute; PushInt 1]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecuteTriple () =
    // this is unintuitive; The continuation in C0 already has save.c0 set,
    // so the obvious return point to PushInt 2 will be changed back to
    // that save.c0, which is contQuit. So, this code will execute only one
    // PushInt 1.
    let st = initialState [PushCont [PushCont [PushInt 2]; Execute; PushInt 1]; Execute; PushInt 0]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 0; Int 1; Int 2], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecuteSetNumArgs0 () =
    let st = initialState [PushInt 1; PushInt 2;
                           PushCont [Depth]; // in that continuation, stack has to be empty
                           SetNumArgs 0; Execute] // but after that, it gets restored
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 0; Int 2; Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecuteSetNumArgs1 () =
    let st = initialState [PushInt 1; PushInt 2;
                           PushCont [Dup];
                           SetNumArgs 1; Execute]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 2; Int 2; Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecuteSetNumArgs2 () =
    let st = initialState [PushInt 1; PushInt 2;
                           PushCont [Dup; PushCont [Inc]; SetNumArgs 2; Execute];
                           SetNumArgs 1; Execute]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 3; Int 2; Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testExecuteJmpJmp () =
    let st = initialState [PushInt 1;
                           PushCont [ PushCont [PushInt 3; PushCont [PushInt 4]; JmpX]; JmpX]; Execute;
                           PushInt 2]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.AreEqual([Int 2; Int 4; Int 3; Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
// the idea of this test is to check wether DUP copies the object itself
// or only the reference to it, in case of continuations.
let testExecuteDupCont () =
    let st = initialState [PushInt 1; PushInt 2; PushInt 3;
                           PushCont [Depth]; Dup; SetNumArgs 0;
                           Execute; Swap; Execute]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        printfn "%A" stk
        Assert.AreEqual([Int 4; Int 0; Int 3; Int 2; Int 1], stk )
    with
        | TVMError s ->
            Assert.Fail(s)

[<Test>]
let testSetIndexVarQ0 () =
    let st = initialState [SetIndexVarQ]
    try
        let finalSt = List.last (runVM st false)
        let stk = List.tail finalSt.stack
        Assert.Fail("shall not reach this point")
    with
        | _ -> // stack underflow
            Assert.Pass()

[<Test>]
let testSetIndexVarQ1 () =
    let st = initialState [PushNull; PushInt 1; PushInt 0; SetIndexVarQ]
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Tup [Int 1]], stk)

[<Test>]
let testSetIndexVarQ2 () =
    let st = initialState [PushNull; PushInt 1; PushInt 3; SetIndexVarQ]
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Tup [Null; Null; Null; Int 1]], stk)

[<Test>]
let testSetIndexVarQ3 () =
    let st = initialState [PushNull; PushInt 1; PushInt 3; SetIndexVarQ;
                           PushInt 0; PushInt 2; SetIndexVarQ]
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Tup [Null; Null; Int 0; Int 1]], stk)

[<Test>]
let testSetIndexVarQ4 () =
    let st = initialState [PushNull; PushNull; PushInt 10; SetIndexVarQ]
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Null], stk)

[<Test>]
let testSetIndexVarQ5 () =
    let st = initialState [PushNull; PushInt 1; PushInt 3; SetIndexVarQ;
                           PushNull; PushInt 4; SetIndexVarQ]
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Tup [Null; Null; Null; Int 1]], stk)

[<Test>]
let testBuildCell0 () =
    let st = initialState [PushInt 30; Newc; Sti 255; Endc; Dup; Dup; Dup;
                           Newc; StRef; StRef; StRef; StRef; BRefs]
    dumpString "testBuildCell0.fif" (outputFift st)
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Int 4], stk)

[<Test>]
let testBuildCell1 () =
    let st = initialState [PushInt 30; Newc; Sti 255; Endc; Dup; Dup; Dup;
                           Newc; StRef; StRef; StRef; StRef; Endc; Ctos; SRefs]
    dumpString "testBuildCell1.fif" (outputFift st)
    let finalSt = List.last (runVM st false)
    let stk = List.tail finalSt.stack
    Assert.AreEqual([Int 4], stk)
