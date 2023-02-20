module GMToTVMCompiler

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework
open System
open System.Collections.Generic

open type TVM.Instruction
open type TVM.Value
open type TVM.SValue

type RuntimeErrors =
    | GlobalNotFound = 10
    | HeapNodeNotFound = 11
    | HeapNodeWrongTag = 12
    | CaseNotFound = 13

type RuntimeGlobalVars =
    | Heap = 1
    | HeapCounter = 2
    | Globals = 3
    | UnwindCont = 4
    | UnwindSelector = 5

// v k D -> D'
let dictSet =
    [PushInt 128; DictUSetB]

// k D -> D[k] -1 | 0
let dictGet =
    [PushInt 128; DictUGet]

// _ -> hc
let getHeapCounter =
    [GetGlob (int RuntimeGlobalVars.HeapCounter)]

// _ -> g
let getGlobals =
    [GetGlob (int RuntimeGlobalVars.Globals)]

// _ -> h
let getHeap =
    [GetGlob (int RuntimeGlobalVars.Heap)]

// n -> _
let putHeapCounter =
    [SetGlob (int RuntimeGlobalVars.HeapCounter)]

// n -> _
let putHeap =
    [SetGlob (int RuntimeGlobalVars.Heap)]

// g -> _
let putGlobals =
    [SetGlob (int RuntimeGlobalVars.Globals)]


// 1. allocate address for the node
// 2. store the node in the heap at that address
// 3. return the new heap on the stack

// node -> a , where heap[a] := n
let heapAlloc =
    getHeapCounter @ // node k
    [Inc; Dup] @ // node k' k'
    putHeapCounter @ // node k'
    getHeap @ // node k' a
    [Xchg 2] @ // a k' node
    [Push 1] @ // a k' node k'
    [RollRev 3] @ // k' a k' node
    TVM.arrayPut @ // k' a'
    putHeap // k'

let ifThenElse cond trueBlock falseBlock =
    cond @ [PushCont trueBlock; IfJmp] @ falseBlock

// k -> heap[k] or exception
let heapLookup =
    getHeap @ // k h
    [Swap] @ // h k
    TVM.arrayGetWithCode @
    [ThrowIfNot (int RuntimeErrors.HeapNodeNotFound)]

// Put the n-th element of the stack on top of the stack;
// 0 denotes the current top value of the stack.
let mapPush (n:int) : TVM.Code =
    [Push n]

// Remove n consecutive elements from the stack
let mapPop (n:int) : TVM.Code =
    [BlkDrop n]

// Remove n elements from the stack, starting from the second
// element of the stack, i.e. leaving the top stack element inplace.
// ... sn .. s2 s1 s -> ...  s
let mapSlide (n:int) : TVM.Code =
    [RollRev n; BlkDrop n]

// Extract the address of a function with id = n from the globals
// and put it on the stack; if the function with the given
// name n is not found, raise exception.
let mapPushglobal (n:int) : TVM.Code =
    [PushInt n] @
    getGlobals @
    [PushInt 128;       // n D 128
     DictUGet;        // D[n] -1 | 0
     ThrowIfNot (int RuntimeErrors.GlobalNotFound);
     Ldu 128; // n s'
     Ends] // n

// Allocate a node for the given integer on the heap and put the
// address of that node on the stack;
let mapPushint (n:int) : TVM.Code =
    [PushInt (int GMachine.NodeTags.NNum); PushInt n; Tuple 2] @
    heapAlloc

// Lookup arguments on the heap and do the corresponding arithmetic
// operation, placing the boxed result on the stack
// n1 n2 -> n3, where heap[n3] = heap[n1] + heap[n2]
let binaryOperation (op:TVM.Code) : TVM.Code =
    heapLookup @ // n1 (0, NNum2)
    [Second] @   // n1 NNum2
    [Swap] @     // NNum2 n1
    heapLookup @ // NNum2 heap[n1]
    [Second] @   // NNum2 NNum1
    [Swap] @     // NNum1 NNum2
    op @
    [PushInt (int GMachine.NodeTags.NNum); Swap; Tuple 2] @  // (0, op(heap[n1], heap[n2])), 0 = NNum tag
    heapAlloc    // n3

let mapAdd () : TVM.Code =
    binaryOperation [Add]

// n1 n2 -> n3, where heap[n3] = heap[n1] - heap[n2]
let mapSub () : TVM.Code =
    binaryOperation [Sub]

let mapMul () : TVM.Code =
    binaryOperation [Mul]

let mapDiv () : TVM.Code =
    binaryOperation [Div]

let mapEqual () : TVM.Code =
    binaryOperation [Equal]

let mapGreater () : TVM.Code =
    binaryOperation [Greater]

// Allocate a node for function application on the heap and
// put the address of that node on the stack
// a1 a2 -> a3 , where heap[a3] = NAp (a1,a2)
let mapMkap () : TVM.Code =
    [PushInt (int GMachine.NodeTags.NAp);  // a1 a2 1
     RollRev 2;  // 1 a1 a2
     Tuple 3] @ // (1, a1, a2)
    heapAlloc // a3

// Change the node pointed by the n-th + 1 element of the stack
// to the Indirection node pointing to the node with the address
// located on top of the stack.
// .. an .. a1 a -> .. an .. a1 , heap[an] := NInd a
let mapUpdate (n:int) : TVM.Code =
    [PushInt (int GMachine.NodeTags.NInd);   // 3 = NInd tag
     Swap;
     Tuple 2;     // ... an .. a1 (3,a)
     Push n] @    // .. an .. a1 (3,a) an
    getHeap @     // .. an .. a1 (3,a) an heap
    [Xchg 2] @    // .. an .. a1 heap an (3,a)
    TVM.arrayPut @ // .. an .. a1 heap'
    putHeap       // .. an .. a1

// -> a1 a2 .. an
// Allocate n dummy nodes on the heap and return put
// their addresses on the stack
let mapAlloc (n:int) : TVM.Code =
    [PushInt n; PushCont ([PushNull] @ heapAlloc); Repeat]

// Put the boxed constructor object onto the stack
// a1 .. an -> a  , where heap[a] = NConstr(tag, [a1, ... an])
let mapPack (tag:int) (n:int) : TVM.Code =
    [PushInt n; TupleVar] @ // (a1,...,an)
    [PushInt (int GMachine.NodeTags.NConstr); Swap; PushInt tag; Swap; Tuple 3] @ // (4, tag, (a1,...,an))
    heapAlloc

// Deconstruct the constructor object located on the stack,
// having n arguments. All arguments (their addresses) are placed onto the stack.
// n -> a1 .. am  , where heap[n] = NConstr (tag, [a1..am])
let mapSplit (n:int) : TVM.Code =
    heapLookup @    // heap[n]
    [Dup; Index 0] @  // heap[n] 4
    [PushInt (int GMachine.NodeTags.NConstr); Equal] @ // (4, tag, (a1am)) 4=4?
    [ThrowIfNot (int RuntimeErrors.HeapNodeWrongTag)] @  // if tag is incorrect, throw;
    // (4, tag, (a1am))
    [Index 2; Dup] @  // (a1am) (a1am)
    [TLen] @        // (a1am) m
    [UntupleVar]    // a1 .. am

// Extract the constructor object's tag and transfer
// control the code given in the corresponding case branch.
// Here, cs is a case selector compiled in a form of a continuation
// that checks the given stack number against possible choices
// and transfer control to the found case; if no case suits,
// throws exception.
// n -> n
let mapCasejump (cs:TVM.Code) : TVM.Code =
    [Dup] @             // n n
    heapLookup @        // n heap[n]
    [Dup] @             // n heap[n] heap[n]
    [Index 0] @         // n heap[n] tag
    [PushInt (int GMachine.NodeTags.NConstr); Equal;
     ThrowIfNot (int RuntimeErrors.HeapNodeWrongTag)] @ // n heap[n]
    [Index 1] @         // n tag : this is the tag we should find in cs
    [PushCont cs; Execute] // n

// If the top stack element evaluates to True, transfer control
// to the t branch; else to the f branch
// n -> _
let mapCond (t:TVM.Code) (f:TVM.Code) : TVM.Code =
    heapLookup @    // heap[n]
    [Dup] @         // heap[n] heap[n]
    [Index 0] @     // heap[n] tag
    [PushInt (int GMachine.NodeTags.NNum); Equal] @ // heap[n] (tag==0?)
    [ThrowIfNot (int RuntimeErrors.HeapNodeWrongTag)] @   // typecheck error
    [Index 1] @     // NNum
    [PushCont t] @  // NNum c
    [IfJmp] @       // goto c if NNum is non-zero (true)
    f // otherwise proceed to false branch

let doUnwind =
    [GetGlob (int RuntimeGlobalVars.UnwindCont); Execute]

let mapUnwindNNum () : TVM.Code =
    [Drop; Ret]

let mapUnwindNAp () : TVM.Code =
    [Index 1] @ doUnwind

let mapUnwindNInd () : TVM.Code =
    [Index 1] @ doUnwind

let mapUnwindNConstr () : TVM.Code =
    [Drop; Ret]

let unwindRearrange () : TVM.Code =
    []  // not done

let mapUnwindNGlobal () : TVM.Code =
    [Dup;        // heap[n] heap[n]
     Index 1;    // heap[n] NGlobal.n
     Depth; Dec; // heap[n] NGlobal.n k
     Swap;
     Less;        // heap[n] k<NGlobal.n?
     PushCont []; // heap[n] k<N c
     IfJmp;       // heap[n]
     Dup;
     Index 1; SetGlob 9; // NGlobal.n
     Index 2; SetGlob 10] @ // NGlobal.c
     (unwindRearrange ()) @
     [GetGlob 10; Execute]

// If the current top stack element is:
//  - a value, i.e. a number or a saturated constructor,
//    then switch to the frame (instructions,stack pair) located on top of the dump.
//  - an Indirection node, then put the indirection
//    address on the stack and Unwind further
//  - a global function, then put the parameters
//    of the function onto the stack and execute the function instructions.
//    If there are not enough arguments on the stack (partial application), then
//    switch to dump code/stack pair
//  - an application node, then put the function address (i.e. first element
//    of the application) on the stack and Unwind further
// n
let mapUnwind () : TVM.Code =
    [Dup] @ // n n
    heapLookup @ // n heap[n]
    [Dup; Index 0] @ // n heap[n] tag
    [GetGlob (int RuntimeGlobalVars.UnwindSelector)] @ // n heap[n] tag sD
    [PushInt 8] @ // n heap[n] tag D 4
    [DictUGetJmp] @ // n heap[n]
    [Throw (int RuntimeErrors.HeapNodeWrongTag)] // unknown tag

let mapEval () : TVM.Code =
    [GetGlob (int RuntimeGlobalVars.UnwindCont); SetNumArgs 1; JmpX]

let rec compileInstr (i:GMachine.Instruction): TVM.Code =
    // some GMachine.Instruction has to be mapped into code fragments
    // of TVM
    match i with
        | GMachine.Push n ->
            mapPush n
        | GMachine.Pop n ->
            mapPop n
        | GMachine.Pushglobal f ->
            mapPushglobal (hash f)
        | GMachine.Pushint n ->
            mapPushint n
        | GMachine.Mkap ->
            mapMkap ()
        | GMachine.Update n ->
            mapUpdate n
        | GMachine.Slide n ->
            mapSlide n
        | GMachine.Alloc n ->
            mapAlloc n
        | GMachine.Unwind ->
            mapUnwind ()
        | GMachine.Eval ->
            mapEval ()
        | GMachine.Add ->
            mapAdd ()
        | GMachine.Sub ->
            mapSub ()
        | GMachine.Mul ->
            mapMul ()
        | GMachine.Div ->
            mapDiv ()
        | GMachine.Equal ->
            mapEqual ()
        | GMachine.Greater ->
            mapGreater ()
        | GMachine.Cond (t,f) ->
            mapCond (compileCode t) (compileCode f)
        | GMachine.Pack (tag,n) ->
            mapPack tag n
        | GMachine.Casejump l ->
            let l' = compileCasejumpSelector l
            mapCasejump l'
        | GMachine.Split n ->
            mapSplit n
and compileCode (code:GMachine.GmCode) : TVM.Code =
    code
    |> List.map (fun c -> compileInstr c) // list of lists of Instructions
    |> List.concat
and compileCasejumpSelector (l: (int * GMachine.GmCode) list) : TVM.Code =
    match l with
        | [] ->
            [Throw (int RuntimeErrors.CaseNotFound)]  // case not found
        | (tag, code) :: t ->
            [Dup; // n n
             PushInt tag; // n n tag
             Equal; // n (tag=n?)
             PushCont ([Drop] @ compileCode code); // n (-1|0) c
             IfJmp] @ // if we found the right tag, jmp to c
                compileCasejumpSelector t


// st - final state; we omit the exit code from the VM
let getResultStack (st:TVM.TVMState) : TVM.Stack =
    List.tail st.stack

// get node with address n from the heap
let getHeapAt (n:int) (st:TVM.TVMState) : TVM.Value =
    let (Tup (Null :: Tup heap :: _))  = st.cr.c7
    let i = n / TVM.bucketSize
    let j = n % TVM.bucketSize
    let (Tup h1) = List.item i heap
    List.item j h1

// extract heap node with the address given on the stack top
let getResultHeap (st:TVM.TVMState) : TVM.Value =
    let ((Int n) :: _) = getResultStack st
    getHeapAt n st

let nnum (n:int) : TVM.Value =
    Tup [Int (int GMachine.NodeTags.NNum); Int n]

let initC7 =
    TVM.arrayNew @
    [SetGlob 1; PushInt -1; SetGlob 2; PushNull; SetGlob 3] @
    [PushCont (mapUnwind ()); SetGlob 4] @
    [PushRef [SDict (Map [(0, [SCode (mapUnwindNNum ())] );
                            (1, [SCode (mapUnwindNAp ())] );
                            (2, [SCode (mapUnwindNGlobal ())] );
                            (3, [SCode (mapUnwindNInd ())] );
                            (4, [SCode (mapUnwindNConstr ())] )])]] @
    [SetGlob (int RuntimeGlobalVars.UnwindSelector)]


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
    // TVM.dumpFiftScript "testAdd0.fif" (TVM.outputFift st)
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
                             GMachine.Greater])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(nnum -1, getResultHeap final)

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
                             GMachine.Update 2])  // heap[0] = NInd 2, heap[2] = NNum 300
    let st = TVM.initialState code
    TVM.dumpFiftScript "testUpdate0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 1; Int 0], getResultStack final)
    Assert.AreEqual (Tup [Int (int GMachine.NodeTags.NInd); Int 2], getHeapAt 0 final)
    Assert.AreEqual (nnum 300, getHeapAt 2 final)

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
