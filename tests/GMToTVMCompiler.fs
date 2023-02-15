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

type RuntimeGlobalVars =
    | Heap = 1
    | HeapCounter = 2
    | Globals = 3
    | UnwindCont = 4

// generate code that stores value n into
// the builder. The builder is assumed to be on
// the stack already.
let rec builderStoreValue (n:TVM.Value): TVM.Code =
    match n with
        | Int v ->
            [PushInt v; Stu 128]
        | Slice s ->
            [PushSlice s; Swap; StSlice]
        | Tup l ->
            l
            |> List.map builderStoreValue
            |> List.concat
        | _ ->
            failwith "unimplemented"

// v k D -> D'
let dictSet =
    [PushInt 128; DictUSetB]

// k D -> D[k] -1 | 0
let dictGet =
    [PushInt 128; DictUGet]

// _ -> c7
let getState =
    [PushCtr 7]

// c7 -> _
let putState =
    [PopCtr 7]

// _ -> hc
let getHeapCounter =
    getState @ [Index (int RuntimeGlobalVars.HeapCounter)]

// _ -> g
let getGlobals =
    getState @ [Index (int RuntimeGlobalVars.Globals)]

// _ -> h
let getHeap =
    getState @ [Index (int RuntimeGlobalVars.Heap)]

// n -> _
let putHeapCounter =
    getState @ [Swap] @ [SetIndex (int RuntimeGlobalVars.HeapCounter)] @ putState

// n -> _
let putHeap =
    getState @ [Swap] @ [SetIndex (int RuntimeGlobalVars.Heap)] @ putState

// g -> _
let putGlobals =
    getState @ [Swap] @ [SetIndex (int RuntimeGlobalVars.Globals)] @ putState

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
    [PushInt (int GMachine.NodeTags.NConstr); Swap; Tuple 2] @ // (4, (a1,...,an))
    heapAlloc

// Deconstruct the constructor object located on the stack,
// having n arguments. All arguments are placed onto the stack.
// -> a1 .. am  , where heap[n] = NConstr (tag, [a1..am])
let mapSplit (n:int) : TVM.Code =
    [PushInt n] @
    heapLookup @    // heap[n]
    [Dup; Index 0] @  // (4, tag, (a1am)) 4
    [PushInt (int GMachine.NodeTags.NConstr); Equal] @ // (4, tag, (a1am)) 4-4
    [ThrowIf 14] @  // if tag is incorrect, throw;
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
    [PushInt (int GMachine.NodeTags.NConstr); Equal; ThrowIf 13] @ // n heap[n]
    [Index 1] @         // n tag : this is the tag we should find in cs
    [PushCont cs; Execute] // n

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

// here, we expected that unwind continuation is stored
// at the back of the stack, initially
let jmpToUnwind =
    [Depth; Dec; Pick; Execute]

let mapUnwind () : TVM.Code =
    // n heap[n]  (note: heap[n] = (NNum n))
    let unwindNNum =
        [Drop; Ret]
    // n heap[n]  (note: heap[n] = (NAp a1,a2))
    let unwindNAp =
        [Index 1] @ jmpToUnwind
    // n heap[n]  (note: heap[n] = NInd a0)
    let unwindNInd =
        [Index 1; Swap; Drop] @ jmpToUnwind
    let unwindNGlobal =
        [Ret]
    let unwindNConstr =
        [Drop; Ret]     // n heap[n]
    heapLookup @ // heap[n]
    [Dup] @      // heap[n] heap[n]
    [Index 0; Dup] @ // heap[n] tag tag
    [PushInt (int GMachine.NodeTags.NNum)] @ // heap[n] tag tag 0
    [Equal] @ // heap[n] tag (tag=0?)
    [PushCont unwindNNum] @ // heap[n] tag (tag=0?) c
    [SetNumArgs 0] @ // heap[n] tag (tag=0?) c' (note: c' omits stack completely)
    [IfJmp] @ // heap[n] tag
    [Dup] @ // heap[n] tag tag
    [PushInt (int GMachine.NodeTags.NAp)] @ // heap[n] tag tag 1 (note: 1 = Nap tag)
    [Equal] @ // heap[n] tag heap (tag=1?)
    [PushCont unwindNAp] @ // heap tag heap (tag=0?) c
    [SetNumArgs 1] @ // heap[n] tag heap[n] (tag=0?) c' (note: c takes 1 arg = heap)
    [IfJmp] @ // heap tag heap
    [Drop] @ // heap tag
    [Dup] @ // heap tag tag
    [PushInt (int GMachine.NodeTags.NGlobal)] @ // heap tag tag 2
    [Equal] @ // heap tag (2==tag?) (node: 2 = NGlobal tag)
    [PushCont unwindNGlobal] @ // heap tag (2==tag?) c
    [IfJmp] @ // heap tag
    [Dup] @ // heap tag tag
    [PushInt (int GMachine.NodeTags.NInd)] @ // heap tag tag 3
    [Equal] @ // heap tag (tag=3?)  (note: 3 = NInd tag)
    // we need to give it the unwind continuation param
    [PushCont unwindNInd] @ // heap tag (tag=3?) c
    [IfJmp] @ // heap tag
    [PushInt (int GMachine.NodeTags.NConstr)] @ // heap tag 4
    [Equal] @ // heap (tag==4?) (note: 4 = NConstr tag)
    [IfRet] @
    [Drop; Throw 8] // unknown tag

// Save the current code and stack (without the top element)
// to the dump, and Unwind with current top stack element.
// In TVM terms, we switch to continuation with Unwind code
// but before that we drop stack elements we do not need.
// The remainder of the current continuation goes into C0, so
// it is like saving to the Dump; also, we need to drop the
// topmost element after switching back to it, hence Drop
// instruction at the end.
let mapEval () : TVM.Code =
    [Depth; Dec; Pick; SetNumArgs 1; JmpX]

// If the top stack element evaluates to True, transfer control
// to the t branch; else to the f branch
// n -> _
let mapCond (t:TVM.Code) (f:TVM.Code) : TVM.Code =
    heapLookup @    // heap[n]
    [Dup] @         // heap[n] heap[n]
    [Index 0] @     // heap[n] tag
    [PushInt 0; Equal] @ // heap[n] (tag==0?)
    [ThrowIf 9] @   // typecheck error
    [Index 1] @     // NNum
    [PushCont t] @  // NNum c
    [IfJmp] @       // goto c if NNum is non-zero (true)
    f // otherwise proceed to false branch

let rec compileTuple t : TVM.Code =
    match t with
        | Tup l ->
            l
            |> List.map compileElem
            |> List.concat
            |> fun l -> l @ [Tuple l.Length]
            | _ -> failwith "not a tuple"
and compileDict (d:Map<int,TVM.Value>) : TVM.Code =
    let kv = Map.toList d
    List.fold (fun dict (k:int, v:TVM.Value) ->
               [PushInt k] @ (builderStoreValue v) @ dict @ dictSet) [NewDict] kv
and compileSlice s : TVM.Code =
    match s with
        | Slice (SDict d :: []) ->
            if Map.isEmpty d then
                [PushNull]
            else
                failwith "not implemented"
        | Slice vs ->
            [PushSlice vs]
        | _ ->
            failwith "not implemented"
and compileElem e : TVM.Code =
    match e with
        | Int n -> [PushInt n]
        | Tup _ -> compileTuple e
        | Cont c -> [PushCont c.code]
        | Null -> [PushNull]
        | Slice _ -> compileSlice e
        | _ -> failwith "not implemented"
and compileInstr (i:GMachine.Instruction): TVM.Code =
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
        | _ ->
            failwith "unreachable"
and encodeNode (n:GMachine.Node) : TVM.Value =
    match n with
        | GMachine.NNum v ->
            Tup [Int 0; Int v]
        | GMachine.NAp (f, a) ->
            Tup [Int 1; Int f; Int a]
        | GMachine.NGlobal (n, c) ->
            let c' = compileCode c
            let c'' = { TVM.Continuation.Default with code = c' }
            Tup [Int 2; Int n; Cont c'']
        | GMachine.NInd v ->
            Tup [Int 3; Int v]
        | GMachine.NConstr (n, (vs:int list)) ->
            Tup ([Int 4; Int n] @ List.map (fun (x:int) -> Int x) vs)
        | _ -> // shall not be reachable
            failwith "unreachable"
and compileCode (code:GMachine.GmCode) : TVM.Code =
    code
    |> List.map (fun c -> compileInstr c) // list of lists of Instructions
    |> List.concat
and compileCasejumpSelector (l: (int * GMachine.GmCode) list) : TVM.Code =
    match l with
        | [] ->
            [Throw 13]  // case not found
        | (tag, code) :: t ->
            [Dup; // n n
             PushInt tag; // n n tag
             Equal;
             PushCont (compileCode code); // n (-1|0) c
             IfJmp] @ // if we found the right tag, jmp to c
                compileCasejumpSelector t

// GMachine stack consists of addresses only; there are
// no data values there.
// We represent addresses by monotonically increasing
// sequence of integers in TVM.
let prepareStack (stk:GMachine.GmStack): TVM.Stack =
    List.map (fun i -> TVM.Int i) stk

let prepareHeap (heap:GMachine.GmHeap): TVM.Value =
    // GMachine heap is a mapping between addresses and Nodes.
    // Nodes are value types of different kind.
    // NGlobal(n,c) that represents piece of executable code
    // NNum n; NAp (addr,addr); NInd addr; NConstr n * [addr]
    // We need to prepare a Tup ([addr -> Value])
    // We rely on the fact that addresses are linearly monotonically
    // increasing, so we can just use array for that instead of
    // mapping
    heap
    |> Map.toList  // [(0,n0); (1,n1); ...]
    |> List.map snd
    |> List.map encodeNode
    |> TVM.Tup

let prepareGlobals (globals:GMachine.GmGlobals): TVM.Value =
    // globals is a mapping from names to addresses
    // we need to prepare the corresponding Slice [SDict] for that
    // Slice (SDict Map<int,SValue list>)
    // GmGlobals = Map<Name, Addr>, where Name is a string, Addr is int
    // Instead of symbolic name, we just use the entry index as its name
    globals
    |> Map.toList  // [("main",10); ("f", 51); ... ]
    |> List.map (fun x -> SInt (snd x))    // [(Int 10), (Int 51), ...]
    |> List.sort
    |> List.map List.singleton
    |> List.indexed    // [(0, [SInt 10]); (1, [SInt 51]); ...]
    |> Map.ofList      // Map<int,SValue list>
    |> SDict
    |> List.singleton
    |> Slice

let compile (gms: GMachine.GmState) : TVM.TVMState =
    let code = compileCode (GMachine.getCode gms)
    let stack = prepareStack (GMachine.getStack gms)
    let c0 = TVM.Continuation.Default
    let heap = prepareHeap (GMachine.getHeap gms)
    let globals = prepareGlobals (GMachine.getGlobals gms)
    let c7 = TVM.Tup [heap; globals; TVM.Int 0]
    { code = code; stack = stack; cr = { TVM.ControlRegs.Default with c0 = Some c0; c7 = c7 } }

[<Test>]
let testPrepareGlobals0 () =
    let globs:GMachine.GmGlobals =
        Map [("main", 100); ("f", 600); ("g", 700); ("sort", 5)]
    let r = prepareGlobals globs
    Assert.AreEqual(
        Slice [SDict (Map [(0, [SInt 5]); (1, [SInt 100]); (2, [SInt 600]); (3, [SInt 700])])],
        r
    )

[<Test>]
let testPrepareHeap0 () =
    let heap:GMachine.GmHeap =
        Map [(0, GMachine.NNum 1);
             (1, GMachine.NAp (1, 2));
             (2, GMachine.NInd 2);
             (3, GMachine.NConstr (3,[1;2;3]))]
    let r = prepareHeap heap
    Assert.AreEqual(TVM.Tup [TVM.Tup [TVM.Int 0; TVM.Int 1];
                             TVM.Tup [TVM.Int 1; TVM.Int 1; TVM.Int 2];
                             TVM.Tup [TVM.Int 3; TVM.Int 2];
                             TVM.Tup [TVM.Int 4; TVM.Int 3; TVM.Int 1; TVM.Int 2; TVM.Int 3]], r)
[<Test>]
let testPushInt0 () =
    let initC7 = TVM.arrayNew @ [PushInt -1; PushNull; Tuple 3; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200])
    let st = TVM.initialState code
    // TVM.dumpFiftScript "testPushInt0.fif" (TVM.outputFift st)
    Assert.Pass()

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

[<Test>]
let testAdd0 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
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
    Assert.AreEqual(Tup [Int 0; Int 1000], getResultHeap final)

[<Test>]
let testPushglobal0 () =
    let initC7 = [PushNull] @
                 TVM.arrayNew @
                 [PushInt -1;
                  PushSlice [SDict (Map [(hash "fact", [SInt 200]);
                                         (hash "main", [SInt 1])])];
                  Tuple 4;
                  PopCtr 7]
    let code = initC7 @ (mapPushglobal (hash "fact"))
    let st = TVM.initialState code
    // TVM.dumpFiftScript "testAdd0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual([Int 200], getResultStack final) // 2 is a result address, not value

[<Test>]
let testPushglobal1 () =
    let initC7 = [PushNull] @
                 TVM.arrayNew @
                 [PushInt -1;
                  PushSlice [SDict (Map [(hash "fact", [SInt 200]);
                                         (hash "main", [SInt 1])])];
                  Tuple 4;
                  PopCtr 7]
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
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
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
    Assert.AreEqual(Tup [Int 0; Int 180], getResultHeap final)

[<Test>]
let testEqual0 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Equal])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testEqual0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int 0; Int 0], getResultHeap final)

[<Test>]
let testEqual1 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Equal])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testEqual1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int 0; Int -1], getResultHeap final)

[<Test>]
let testGreater0 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Pushint 200;
                             GMachine.Pushint 100;
                             GMachine.Greater])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int 0; Int -1], getResultHeap final)

[<Test>]
let testGreater1 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 100;
                             GMachine.Greater])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int 0; Int 0], getResultHeap final)

[<Test>]
let testmkAp () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Mkap])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testGreater1.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual(Tup [Int (int GMachine.NodeTags.NAp); Int 0; Int 1], getResultHeap final)
    Assert.AreEqual(Tup [Int (int GMachine.NodeTags.NNum); Int 100], getHeapAt 0 final)
    Assert.AreEqual(Tup [Int (int GMachine.NodeTags.NNum); Int 200], getHeapAt 1 final)

[<Test>]
let testUpdate0 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
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
    Assert.AreEqual (Tup [Int (int GMachine.NodeTags.NNum); Int 300], getHeapAt 2 final)

[<Test>]
let testAlloc0 () =
    let initC7 = [PushNull] @ TVM.arrayNew @ [PushInt -1; PushNull; Tuple 4; PopCtr 7]
    let code = initC7 @
               (compileCode [GMachine.Alloc 3])
    let st = TVM.initialState code
    TVM.dumpFiftScript "testAlloc0.fif" (TVM.outputFift st)
    let final = List.last (TVM.runVM st false)
    Assert.AreEqual ([Int 2; Int 1; Int 0], getResultStack final)
    Assert.AreEqual (Null, getHeapAt 0 final)
    Assert.AreEqual (Null, getHeapAt 1 final)
    Assert.AreEqual (Null, getHeapAt 2 final)
