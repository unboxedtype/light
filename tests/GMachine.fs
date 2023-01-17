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
    | Pop of n: int
    | Mkap
    | Update of n: int
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

// Expression node (when computing, not AST)
type Node =
    | NNum of v: int
    | NAp of f: Addr * a: Addr // f(a)
    | NGlobal of args: int * code: GmCode
    | NInd of v: int  // indirection node

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

let putGlobals (name:Name) (addr:Addr) (code, stack, heap, globals, stats): GmState =
    let globals' = Map.add name addr globals
    (code, stack, heap, globals', stats)

let pushglobal (f:Name) (state:GmState) =
    match Map.tryFind f (getGlobals state) with
        | Some a ->
            putStack (a :: getStack state) state
        | None ->
            let msg = sprintf "Global name %A not found in the globals dictionary" f
            raise (GMError msg)

let globalLookup (key:Name) (globals:GmGlobals) : Addr option =
    match Map.tryFind key globals with
        | Some v ->
            Some v
        | None ->
            None

let pushint n state =
    match globalLookup (string n) (getGlobals state) with
        | Some addr ->
            putStack (addr :: getStack state) state
        | None ->
            let (heap', a) = heapAlloc (getHeap state) (NNum n)
            putGlobals (string n) a (putHeap heap' (putStack (a :: getStack state) state))

let mkap state =
    match getStack state with
        | a1 :: a2 :: as' ->
            let (heap', a) = heapAlloc (getHeap state) (NAp (a1, a2))
            putHeap heap' (putStack (a :: as') state)
        | _ ->
            raise (GMError "stack underflow")

let getApArg n =
    match n with
        | NAp (f, v) ->
            v
        | _ ->
            raise (GMError "node must be of NAp type")

let heapLookup (heap:GmHeap) (key:Addr) : Node =
    match Map.tryFind key heap with
        | Some v ->
            v
        | None ->
            let msg = sprintf "key %A not found in the map" key
            raise (GMError msg)

let heapUpdate (heap:GmHeap) (key:Addr) (v:Node) =
    Map.add key v heap

let at l n =
    List.item n l

let push n state =
    let as' = getStack state
    let a = at as' n
    putStack (a :: as') state

// remove n items from the stack
let pop n state =
    let as' = getStack state
    putStack (List.skip n as') state

let slide n state =
    match getStack state with
        | a :: as' ->
            putStack (a :: List.skip n as') state
        | _ ->
            raise (GMError "stack underflow")

let update n state =
    match getStack state with
        | a :: as' ->
            let heap = getHeap state
            let an = at as' n
            putHeap (heapUpdate heap an (NInd a)) (putStack as' state)
        | _ ->
            raise (GMError "stack underflow")

let rearrange n heap s =
    let s' = List.map (fun x -> heapLookup heap x |> getApArg) (List.take n (List.tail s))
    s' @ (List.skip n s)

let unwind state =
    match getStack state with
        | a :: as' ->
            let heap = getHeap state
            let newState s =
                match s with
                    | NNum n ->
                        putCode [] state
                    | NAp (a1, a2) ->
                        putCode [Unwind] (putStack (a1 :: a :: as') state)
                    | NGlobal (n, c) ->
                        if List.length as' < n then
                            raise (GMError "Unwinding with too few arguments")
                        else
                            putStack (rearrange n heap (a :: as')) (putCode c state)
                    | NInd a0 ->
                        putCode [Unwind] (putStack (a0 :: as') state)
            newState (heapLookup heap a)
        | _ ->
            raise (GMError "stack underflow")

let dispatch i =
    match i with
        | Pushglobal f ->
            pushglobal f
        | Pushint n ->
            pushint n
        | Mkap ->
            mkap
        | Update n ->
            update n
        | Push n ->
            push n
        | Pop n ->
            pop n
        | Slide n ->
            slide n
        | Unwind ->
            unwind

// there is always at least one instruction in the code
// otherwise the step function shouldn't have executed
let step state =
    (**
    let code_str = sprintf "%A" (getCode state)
    let stack_str = sprintf "%A" (getStack state)
    let heap_str = sprintf "%A" (getHeap state)
    NUnit.Framework.TestContext.Progress.WriteLine("CODE : {0}\nSTACK: {1}\nHEAP: {2}",
                                                  code_str, stack_str, heap_str)
                                                  **)
    match getCode state with
        | i :: is ->
            dispatch i (putCode is state)
        | _ ->
            raise (GMError "stack underflow")

// new state is added to the end of the list
let rec eval state =
    let restStates =
        if gmFinal state then [] else
            let nextState = doAdmin (step state)
            eval nextState
    state :: restStates

// AST Expression node
type Expr =
    | EVar of name:Name
    | ENum of n:int
    | EAp of e1:Expr * e2:Expr

type GmCompiledSC = Name * int * GmCode

let initialCode : GmCode =
    [Pushglobal "main"; Unwind]

// Allocate supercombinator, i.e. add the given new supercombinator
// into the heap and return newly allocated address together with
// the new heap. This is a folding function.
let allocateSc (heap: GmHeap, globals: GmGlobals) ((name, nargs, code):GmCompiledSC) =
    let (heap', addr) = heapAlloc heap (NGlobal (nargs, code))
    let globals' = Map.add name addr globals
    (heap', globals')

// shift all indexes on m places
let argOffset m env =
    [for (n, v) in env -> (n + m, v)]

let rec compileC ast env =
    match ast with
        | ENum n ->
            [Pushint n]
        | EAp (e1, e2) ->
            compileC e2 env @ compileC e1 (argOffset 1 env) @ [Mkap]
        | EVar v ->
            let r = List.tryPick (fun (n, v') ->
                                  if v' = v then Some n else None) env
            match r with
                | Some n ->
                    [Push n]
                | _ ->
                    [Pushglobal v]

// ast env -> Instruction list
let compileR ast env =
    let n = List.length env
    compileC ast env @ [Update n; Pop n; Unwind]

// Supercombinator is defined by the following triplet
// (sc name, list of formal argument variable names, body AST)
type SC = Name * (Name list) * Expr

// Program is a list of supercombinator definitions, including the
// Main combinator
type CoreProgram = SC list

// compile Supercombinator with the given name, having the
// given environment and ast (body)
let compileSc ((name, env, ast): SC) : GmCompiledSC =
    (name, List.length env, compileR ast (List.indexed env))

// (GmHeap, GmGlobals)
let buildInitialHeap program =
    let initialHeap = Map []
    let initialGlobals = Map []
    let acc = (initialHeap, initialGlobals)
    let compiled1 = List.map compileSc program
    let (heap, globals) = List.fold allocateSc acc compiled1
    (heap, globals)

let compile (program: CoreProgram) : GmState =
    let (heap, globals) = buildInitialHeap program
    (initialCode, [], heap, globals, statInitial)

let getResult (st:GmState) : Node =
    match st with
        | ([], [resultAddr], heap, _, _) ->
            heapLookup heap resultAddr
        | _ ->
            raise (GMError "incorrect VM final state")

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let compileScKTest () =
    let code = compileSc ("K", ["x"; "y"], (EVar "x"))
    Assert.AreEqual( ("K", 2, [Push 0; Update 2; Pop 2; Unwind]), code );

[<Test>]
let compileScFTest () =
    let code = compileSc ("F", ["x"; "y"], (EAp (EVar "z", EVar "x")))
    Assert.AreEqual( ("F", 2, [Push 0; Pushglobal "z"; Mkap; Update 2; Pop 2; Unwind]), code );

[<Test>]
let compileProgTest () =
    let coreProg =
        [ ("main", [], (EAp (EVar "Z", EVar "y")));
          ("y", [], (ENum 1));
          ("Z", ["x"], (EVar "x")) ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    Assert.AreEqual( NNum 1, getResult finalSt )

[<Test>]
let testK () =
    let coreProg = [
        // K x y = x
        ("K", ["x"; "y"], EVar "x");
        // main = K 3 4
        ("main", [], EAp (EAp (EVar "K", ENum 3), ENum 4))
    ]
    let initSt = compile coreProg
    printfn "%A" initSt
    let finalSt = List.last (eval initSt)
    NUnit.Framework.TestContext.Progress.WriteLine("testK: steps = {0}", getStats finalSt)
    Assert.AreEqual( NNum 3, getResult finalSt )

[<Test>]
let testSKK3 () =
    let coreProg = [
        // K x y = x
        ("K", ["x"; "y"], EVar "x");
        // S f g x = f x (g x)
        ("S", ["f"; "g"; "x"], EAp (EAp (EVar "f", EVar "x"), EAp (EVar "g", EVar "x")));
        // main = S K K 3
        ("main", [], EAp (EAp (EAp (EVar "S", EVar "K"), EVar "K"), ENum 3))
    ]
    let initSt = compile coreProg
    printfn "%A" initSt
    let finalSt = List.last (eval initSt)
    NUnit.Framework.TestContext.Progress.WriteLine("testSKK3: steps = {0}", getStats finalSt)
    Assert.AreEqual( NNum 3, getResult finalSt )

[<Test>]
let testTwiceTwice () =
    let coreProg = [
        // twice f x = f (f x)
        ("twice", ["f"; "x"], EAp (EVar "f", EAp (EVar "f", EVar "x")))
        // id x = x
        ("id", ["x"], EVar "x");
         // main = twice twice id 3
        ("main", [], EAp (EAp (EAp (EVar "twice", EVar "twice"), EVar "id"), ENum 3))
    ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    NUnit.Framework.TestContext.Progress.WriteLine("testTwiceTwice: steps = {0}", getStats finalSt)
    Assert.AreEqual(NNum 3, getResult finalSt)
