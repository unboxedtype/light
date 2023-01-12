module GMachine

open NUnit.Framework
open System.Collections.Generic

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

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let BasicTest () =
    let code = [Unwind]
    ()
    
