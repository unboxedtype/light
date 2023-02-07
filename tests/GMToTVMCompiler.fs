module GMToTVMCompiler

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework
open System
open System.Collections.Generic

open type TVM.Instruction
open type TVM.Value
open type TVM.C7i

// inject value into the builder;
// used to store values in dictionaries
let valueBld v =
    [Newc; PushInt v; Stu 128]

// create emtpy dict; put it on the stack
let newDict =
    [NewDict]

// D[k] := val
let dictSet k valBld D =
    valBld @ k @ D @ [PushInt 128; DictUSetB]

// D[k]
let dictGet k D =
    k @ D @ [PushInt 128; DictUGet]

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
     PushInt n;
     DictUGet;        // x -1 | 0
     ThrowIfNot 10]   // x

let mapMkap () : TVM.Code =
    []

let mapUpdate (n:int) : TVM.Code =
    []

let mapAlloc (n:int) : TVM.Code =
    []

let mapUnwind () : TVM.Code =
    []

let mapEval () : TVM.Code =
    []

let mapAdd () : TVM.Code =
    []

let mapSub () : TVM.Code =
    []

let mapMul () : TVM.Code =
    []

let mapDiv () : TVM.Code =
    []

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

type GlobalsDict = Map<int,TVM.Value>

let rec compileTuple t : TVM.Code =
    match t with
        | Tup l ->
            List.rev l
            |> List.map compileElem
            |> List.concat
            |> fun l -> l @ [Tuple l.Length]
            | _ -> failwith "not a tuple"
and compileDict (d:Map<int,TVM.Value>) : TVM.Code =
  (*  let kv = Map.toList d
    List.fold (fun dict (k,v) ->
               dictSet [PushInt (TVM.Value.unboxInt k)] (valueBld v) dict) newDict kv *)
    failwith "not implemented"
and compileElem e : TVM.Code =
    match e with
        | Int n -> [PushInt n]
        | Tup l -> compileTuple e
        | Cont c -> [PushCont c.code]
        | Null -> [PushNull]
        | SliceDict d -> compileDict d
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
        | GMachine.NConstr (n, vs) ->
            Tup ([Int 4; Int n] @ (List.map TVM.Value.boxInt vs))
        | _ -> // shall not be reachable
            failwith "unreachable"
and mapPushint (n:int) : TVM.Code =
    let currAddress  =
        [PushCtr 7; Index (int C7_HeapCounter)]
    let nextAddress =
        currAddress @ [Inc]
    let getHeap =
        [PushCtr 7; Index (int C7_Heap)]
    let putHeap h =
        getHeap @ h @ [SetIndex (int C7_Heap)]
    let heapAlloc heap node =
        dictSet nextAddress (valueBld n) heap
    let getGlobals =
        [PushCtr 7; Index (int C7_Globals)]
    let putGlobals g =
        getGlobals @ g @ [SetIndex (int C7_Globals)]
    let ifThenElse cond trueBlock falseBlock =
        cond @ [PushCont trueBlock; IfJmp] @ falseBlock
    let node = compileTuple (encodeNode (GMachine.NNum n))
    ifThenElse (dictGet [PushInt n] getGlobals)
        [ (* If item is found, do nothing - the address is on the stack already *)]
        (* otherwise allocate new heap node; update it and put the curr address
           on the stack *)
        (putHeap (heapAlloc getHeap node) @ currAddress)
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
    // we need to prepare the corresponding SliceDict for that
    // SliceDict = Map<int,Value>
    // GmGlobals = Map<Name, Addr>, where Name is a string, Addr is int
    // Instead of symbolic name, we just use the entry index as its name
    globals
    |> Map.toList  // [("main",10); ("f", 51); ... ]
    |> List.map (fun x -> TVM.Int (snd x))    // [(Int 10), (Int 51), ...]
    |> List.sort
    |> List.indexed    // [(0, Int 10); (1, Int 51); ...]
    |> Map.ofList      // Map<int,Value)
    |> TVM.SliceDict

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
    Assert.AreEqual(TVM.SliceDict (Map [(0, TVM.Int 5);
                                        (1, TVM.Int 100);
                                        (2, TVM.Int 600);
                                        (3, TVM.Int 700)]), r)

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
    // (heap, globals, globals counter)
    let initC7Tuple = Tup [ Tup []; SliceDict (Map []); Int 0]
    let initC7Compile = compileTuple initC7Tuple @ [PopCtr 7]
    let r = compileCode [GMachine.Pushint 10]
    printfn "%A" (initC7Compile @ r)
    Assert.Fail()
