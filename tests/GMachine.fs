module GMachine

open NUnit.Framework
open System
open System.Collections.Generic

exception GMError of string

type Name = string

type Instruction =
    | Unwind
    | Pushglobal of name: Name
    | Pushint of v: int
    | Push of e: int
    | Mkap
    | Slide of n: int

type Addr = int

type GmCode = Instruction list

let getCode (i, _, _, _, _) =
    i
let putCode i' (i, stack, heap, globals, stats) =
    (i', stack, heap, globals, stats)

type GmStack = Addr list

let getStack (i, stack, heap, globals, stats) =
    stack

let putStack s' (i, stack, heap, globals, stats) =
    (i, s', heap, globals, stats)

type Node =
    | NNum of v: int
    | NAp of f: Addr * a: Addr // f(a)
    | NGlobal of args: int * code: GmCode

type GmHeap = Map<Addr, Node>

let getHeap (i, stack, heap, globals, stats) =
    heap
let putHeap h' (i, stack, heap, globals, stats) =
    (i, stack, h', globals, stats)

type GmGlobals = Map<Name, Addr>

let getGlobals (i, stack, heap, globals, stats) =
    globals
type GmStats = int

let statInitial =
    0
let statIncSteps s =
    s + 1
let statGetSteps s =
    s

let getStats (i, stack, heap, globals, stats) =
    stats
let putStats stats' (i, stack, heap, globals, stats) =
    (i, stack, heap, globals, stats')

type GmState =
    GmCode * GmStack * GmHeap * GmGlobals * GmStats

// Evaluator:
// test that we are in the final state, no more steps to do
let gmFinal s =
    match (getCode s) with
    | [] -> true
    | _ -> false

// increment steps statistics
let doAdmin s =
    putStats (statIncSteps (getStats s)) s

let heapAlloc heap node =
    let findNewAddr heap =
        if Map.isEmpty heap then
            0
        else
            (List.max (Map.keys heap |> Seq.cast |> List.ofSeq)) + 1
    let addr = findNewAddr heap
    (Map.add addr node heap, addr)

let pushglobal f state =
    let a = Map.find f (getGlobals state)
    putStack (a :: getStack state) state

let pushint n state =
    let (heap', a) = heapAlloc (getHeap state) (NNum n)
    putHeap heap' (putStack (a :: getStack state) state)

let mkap state =
    let (a1 :: a2 :: as') = getStack state
    let (heap', a) = heapAlloc (getHeap state) (NAp (a1, a2))
    putHeap heap' (putStack (a :: as') state)

let getArg n =
    match n with
        | NAp (f, v) -> v
        | _ -> raise (GMError "node must be of NAp type")

let hLookup heap key =
    Map.find key heap

let at l n =
    List.item n l

let push n state =
    let as' = getStack state
    let a = getArg (hLookup (getHeap state) (at as' (n + 1)))
    putStack (a :: as') state

let slide n state =
    let (a :: as') = getStack state
    putStack (a :: List.skip n as') state

let unwind state =
    let (a :: as') = getStack state
    let heap = getHeap state
    let newState s =
        match s with
            | NNum n -> state
            | NAp (a1, a2) -> putCode [Unwind] (putStack (a1 :: a :: as') state)
            | NGlobal (n, c) ->
                if List.length as' < n then
                    raise (GMError "Unwinding with too few arguments")
                else
                    putCode c state
    newState (hLookup heap a)

let dispatch i =
    match i with
        | Pushglobal f ->
            pushglobal f
        | Pushint n ->
            pushint n
        | Mkap ->
            mkap
        | Push n ->
            push n
        | Slide n ->
            slide n
        | Unwind ->
            unwind

// there is always at least one instruction in the code
// otherwise the step function shouldn't have executed
let step state =
    let (i :: is) = getCode state
    dispatch i (putCode is state)

// new state is added to the end of the list
let rec eval state =
    let restStates =
        if gmFinal state then [] else
            let nextState = doAdmin (step state)
            eval nextState
    state :: restStates

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let BasicTest () =
    let code = [Unwind]
    ()
