module GMToTVMCompiler

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework
open System
open System.Collections.Generic

open type TVM.Instruction
open type TVM.Value
open type TVM.SValue
open type TVM.C7i

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
    getState @ [Index (int C7_HeapCounter)]

// _ -> g
let getGlobals =
    getState @ [Index (int C7_Globals)]

// _ -> h
let getHeap =
    getState @ [Index (int C7_Heap)]

// n -> _
let putHeapCounter =
    getState @ [Swap] @ [SetIndex (int C7_HeapCounter)] @ putState

// n -> _
let putHeap =
    getState @ [Swap] @ [SetIndex (int C7_Heap)] @ putState

// g -> _
let putGlobals =
    getState @ [Swap] @ [SetIndex (int C7_Globals)] @ putState

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
    [ThrowIfNot 15]

// put the n-th element of the stack on top
// of the stack
let mapPush (n:int) : TVM.Code =
    [Push n]

// remove n items from the stack
let mapPop (n:int) : TVM.Code =
    [BlkDrop n]

let mapSlide (n:int) : TVM.Code =
    [RollRev n; BlkDrop n]

let mapPushglobal (n:int) : TVM.Code =
    [PushInt 128;
     PushCtr 7;
     Index ( int C7_Globals );  // 128 D
     PushInt n;       // 128 D n
     DictUGet;        // D[n] -1 | 0
     ThrowIfNot 10]   // x

let mapPushint (n:int) : TVM.Code =
    [PushInt 0; PushInt n; Tuple 2] @
    heapAlloc

// n1 n2 -> n3, where heap[n3] = heap[n1] + heap[n2]
let mapAdd () : TVM.Code =
    heapLookup @ // n1 (0, NNum2)
    [Second] @   // n1 NNum2
    [Swap] @     // NNum2 n1
    heapLookup @ // NNum2 heap[n1]
    [Second] @   // NNum2 NNum1
    [Add; PushInt 0; Swap; Tuple 2] @  // (1, heap[n1]+heap[n2])
    heapAlloc    // n3

// a1 a2 -> a3 , where heap[a3] = NAp (a1,a2)
let mapMkap () : TVM.Code =
    [ PushInt 1;  // a1 a2 1
      RollRev 2;  // 1 a1 a2
      Tuple 3; // (1, a1, a2)
    ] @ heapAlloc // a3

// .. an .. a1 a -> .. an .. a1 , heap[an] := NInd a
let mapUpdate (n:int) : TVM.Code =
    [PushInt 3;
     Swap;
     Tuple 2;  // ... an .. a1 (2,a)
     Push n] @ // .. an .. a1 (2,a) an
    getHeap @  // .. an .. a1 (2,a) an heap
    [Xchg 2] @ // .. an .. a1 heap an (2,a)
    TVM.putArray @ // .. an .. a1 heap'
    putHeap    // .. an .. a1

// _ -> a1 a2 .. an
let mapAlloc (n:int) : TVM.Code =
    [PushInt n; pushCont heapAlloc; Repeat]

let mapUnwind () : TVM.Code =
    []

let mapEval () : TVM.Code =
    []

let mapSub () : TVM.Code =
    failWith "not implemented"

let mapMul () : TVM.Code =
    failWith "not implemented"

let mapDiv () : TVM.Code =
    failWith "not implemented"

let mapEq () : TVM.Code =
    []

let mapGt () : TVM.Code =
    []

let mapCond t f : TVM.Code =
    []

let mapPack (tag:int) (n:int) : TVM.Code =
    []

let mapCasejump l : TVM.Code =
    []

let mapSplit (n:int) : TVM.Code =
    []

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
        | GMachine.Eq ->
            mapEq ()
        | GMachine.Gt ->
            mapGt ()
        | GMachine.Cond (t,f) ->
            mapCond t f
        | GMachine.Pack (tag,n) ->
            mapPack tag n
        | GMachine.Casejump l ->
            mapCasejump l
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
let prepareGlobalsTest0 () =
    let globs:GMachine.GmGlobals =
        Map [("main", 100); ("f", 600); ("g", 700); ("sort", 5)]
    let r = prepareGlobals globs
    Assert.AreEqual(
        Slice [SDict (Map [(0, [SInt 5]); (1, [SInt 100]); (2, [SInt 600]); (3, [SInt 700])])],
        r
    )

[<Test>]
let prepareHeapTest0 () =
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
let pushIntTest0 () =
    let globalsEmpty = Slice [SDict (Map [])]
    let heapEmpty = TVM.arrayNew
    let heapInitCounter = Int -1
    let initC7Tuple = heapEmpty @
                      (compileElem heapInitCounter) @
                      (compileElem globalsEmpty) @
                      [Tuple 3]
    let initC7Compile = initC7Tuple @ [PopCtr 7]
    let code = initC7Compile @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200])
    let st = TVM.initialState code
    TVM.dumpFiftScript "pushIntTest0.fif" (TVM.outputFift st)
    Assert.Pass()

[<Test>]
let addTest0 () =
    let globalsEmpty = Slice [SDict (Map [])]
    let heapEmpty = TVM.arrayNew
    let heapInitCounter = Int -1
    let initC7Tuple = heapEmpty @
                      (compileElem heapInitCounter) @
                      (compileElem globalsEmpty) @
                      [Tuple 3]
    let initC7Compile = initC7Tuple @ [PopCtr 7]
    let code = initC7Compile @
               (compileCode [GMachine.Pushint 100;
                             GMachine.Pushint 200;
                             GMachine.Add;
                             GMachine.Pushint 300;
                             GMachine.Add;
                             GMachine.Pushint 400;
                             GMachine.Add])
    let st = TVM.initialState code
    TVM.dumpFiftScript "addTest0.fif" (TVM.outputFift st)
    let finalSt = List.last (TVM.runVM st false)
    let stk = List.tail finalSt.stack
    printfn "%A" stk
    Assert.AreEqual([Int 6], stk) // 2 is a result address, not value
    let (Tup (Tup (Tup heap :: _) :: _)) = finalSt.cr.c7
    Assert.AreEqual (Tup [Int 0; Int 1000], List.item 6 heap)  // (0,300) is heap object of an integer 300
