module GMToTVMCompiler

// Incomplete pattern matches on this expression.
#nowarn "25"

open NUnit.Framework
open System
open System.Collections.Generic

// open type GMachine.GmState
// open type TVM.TVMState

let compileCode (code:GMachine.GmCode): TVM.Code =
    []

// GMachine stack consists of addresses only; there are
// no data values there.
// We represent addresses by monotonically increasing
// sequence of integers in TVM.
let prepareStack (stk:GMachine.GmStack): TVM.Stack =                       
    List.map (fun i -> TVM.Int i) stk

let compileToTVM (c:GMachine.GmCode): TVM.Code =
    []

let encodeNode (n:GMachine.Node) : TVM.Value =
    match n with
        | GMachine.NNum v ->
            TVM.Tup [TVM.Int 0; TVM.Int v]
        | GMachine.NAp (f, a) ->
            TVM.Tup [TVM.Int 1; TVM.Int f; TVM.Int a]
        | GMachine.NGlobal (n, c) ->
            let c' = compileToTVM c
            let c'' = TVM.Cont { TVM.Continuation.Default with code = c' }
            TVM.Tup [TVM.Int 2; TVM.Int n; TVM.Cell [c'']]
        | GMachine.NInd v ->
            TVM.Tup [TVM.Int 3; TVM.Int v]
        | GMachine.NConstr (n, vs) ->
            TVM.Tup ([TVM.Int 4; TVM.Int n] @ (List.map TVM.Value.boxInt vs))
        | _ -> // shall not be reachable
            failwith "unknown GMachine node type"

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
