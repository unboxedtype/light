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
    | Alloc of n: int
    | Eval
    | Add
    | Sub
    | Mul
    | Eq
    | Gt
    | Cond of t:GmCode * f:GmCode
and
    GmCode = Instruction list

type Addr = int
type GmStack = Addr list
// Expression node (when computing, not AST)
type Node =
    | NNum of v: int
    | NAp of f: Addr * a: Addr // f(a)
    | NGlobal of args: int * code: GmCode
    | NInd of v: int  // indirection node
type GmHeap = Map<Addr, Node>
type GmGlobals = Map<Name, Addr>
type GmStats = int
type GmDump =
    (GmCode * GmStack) list
type GmState =
    GmCode * GmStack * GmDump * GmHeap * GmGlobals * GmStats

let getCode (st:GmState) =
    let (code, _, _, _, _, _) = st
    code

let putCode (code':GmCode) (st:GmState) =
    let (_, stack, dump, heap, globals, stats) = st
    (code', stack, dump, heap, globals, stats)

let getStack (st:GmState) =
    let (_, stack, _, _, _, _) = st
    stack

let putStack (s':GmStack) (st:GmState) =
    let (code, _, dump, heap, globals, stats) = st
    (code, s', dump, heap, globals, stats)



// This is a placeholder value that will be overwritten
// during the evaluation
let hNull = NInd -1

let getHeap (st:GmState) =
    let (_, _, _, heap, _, _) = st
    heap
let putHeap heap st =
    let (code, stack, dump, _, globals, stats) = st
    (code, stack, dump, heap, globals, stats)

let statInitial =
    0
let statIncSteps s =
    s + 1
let statGetSteps s =
    s

let getStats st =
    let (_, _, _, _, _, stats) = st
    stats
let putStats stats' st =
    let (code, stack, dump, heap, globals, stats) = st
    (code, stack, dump, heap, globals, stats')

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

let getDump st =
    let (_, _, dump, _, _, _) = st
    dump
let putDump dump st =
    let (code, stack, _, heap, globals, stats) = st
    (code, stack, dump, heap, globals, stats)

let getGlobals (st:GmState) : GmGlobals =
    let (_, _, _, _, globals, _) = st
    globals

let putGlobals (name:Name) (addr:Addr) (st:GmState) : GmState =
    let globals' = Map.add name addr (getGlobals st)
    let (code, stack, dump, heap, _, stats) = st
    (code, stack, dump, heap, globals', stats)

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
    if List.length as' <= n then
        raise (GMError "stack underflow in PUSH")
    else
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

// a0 : ... : an : s h[a0: NGlobal n c, a1: NAp a0 a1', a2: NAp a1 a2', ...]
//->
// a'1 : ... : a'n : an : s
let rearrange n heap s =
    let s' = List.map (fun x -> heapLookup heap x |> getApArg) (List.take n (List.tail s))
    s' @ (List.skip n s)

let unwind state =
    let failIf cond str =
        if cond then raise (GMError str) else ()
    match getStack state with
        | a :: as' ->
            let heap = getHeap state
            let newState s =
                match s with
                    | NNum n ->
                        let dump = getDump state
                        failIf (List.length dump = 0) "Unwind with an empty dump"
                        let (code, stack) = List.head (getDump state)
                        let dump' = List.tail dump
                        putDump dump' (putCode code (putStack (a :: stack) state))
                    | NAp (a1, a2) ->
                        putCode [Unwind] (putStack (a1 :: a :: as') state)
                    | NGlobal (n, c) ->
                        failIf (List.length as' < n) "Unwinding with too few arguments"
                        putStack (rearrange n heap (a :: as')) (putCode c state)
                    | NInd a0 ->
                        putCode [Unwind] (putStack (a0 :: as') state)
            newState (heapLookup heap a)
        | _ ->
            raise (GMError "stack underflow")

let evalInstr state =
    let code' = getCode state
    let (a :: s') = getStack state
    let dump' = (code', s') :: (getDump state)
    putCode [Unwind] (putStack [a] (putDump dump' state))

let rec allocNodes (n:int) (heap:GmHeap) =
    match n with
        | 0 ->
            (heap, [])
        | _ ->
            let (heap1, as') = allocNodes (n - 1) heap
            let (heap2, a) = heapAlloc heap1 hNull
            (heap2, a :: as')

let alloc n state =
    let (heap, addrs) = allocNodes n (getHeap state)
    putHeap heap (putStack (addrs @ getStack state) state)

let True = 1
let False = 0
let NTrue = (NNum True)
let NFalse = (NNum False)

let cmpop (cmpr : int -> int -> bool) state =
    let heap = getHeap state
    let (a1 :: a2 :: s') = getStack state
    let (NNum n1, NNum n2) = (heapLookup heap a1, heapLookup heap a2)
    let (heap', a) = heapAlloc heap (NNum (if (cmpr n1 n2) then True else False))
    putStack (a :: s') (putHeap heap' state)


let binop (op : int -> int -> int) state =
    let heap = getHeap state
    let (a1 :: a2 :: s') = getStack state
    let (NNum n1, NNum n2) = (heapLookup heap a1, heapLookup heap a2)
    let (heap', a) = heapAlloc heap (NNum (op n1 n2))
    // a points to the result op(n1, n2)
    putStack (a :: s') (putHeap heap' state)

let add state =
    binop (fun a b -> a + b) state
let sub state =
    binop (fun a b -> a - b) state
let mul state =
    binop (fun a b -> a * b) state

let eq state =
    cmpop (fun a b -> a = b) state
let gt state =
    cmpop (fun a b -> a > b) state

let cond i1 i2 state =
    let (a :: s') = getStack state
    match (heapLookup (getHeap state) a) with
        | NNum a when a = 1 ->
            putStack s' (putCode (i1 @ (getCode state)) state)
        | NNum a when a = 0 ->
            putStack s' (putCode (i2 @ (getCode state)) state)
        | _ ->
            raise (GMError "incorrect conditional variable")

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
        | Alloc n ->
            alloc n
        | Eval ->
            evalInstr
        | Cond (i1, i2) ->
            cond i1 i2
        | Add ->
            add
        | Sub ->
            sub
        | Mul ->
            mul
        | Eq ->
            eq
        | Gt ->
            gt

// there is always at least one instruction in the code
// otherwise the step function shouldn't have executed
let step state =
    match getCode state with
        | i :: is ->
            dispatch i (putCode is state)
        | _ ->
            raise (GMError "stack underflow")

// new state is added to the end of the list
let rec eval (state:GmState) =
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
    | ELet of isRec:bool * defs:GmDefinitions * body:Expr
//  | If of c:bool * t:Expr * f:Expr
//  | EAdd of a1:Expr * a2:Expr
and GmDefinitions = (Name * Expr) list

// combinator name, number of arguments, code
type GmCompiledSC = Name * int * GmCode

// Allocate supercombinator, i.e. add the given new supercombinator
// into the heap and return newly allocated address together with
// the new heap. This is a folding function.
let allocateSc (heap: GmHeap, globals: GmGlobals) ((name, nargs, code):GmCompiledSC) =
    let (heap', addr) = heapAlloc heap (NGlobal (nargs, code))
    let globals' = Map.add name addr globals
    (heap', globals')

// index + variable name
// [(1,"x"), (2,"y") ..]
// index is needed to know the offset of the variables pointer
    // in the stack
type GmEnvironment = (int * Name) list

// shift all indexes on m places
let argOffset (m:int) (env: GmEnvironment) =
    [for (n, v) in env -> (n + m, v)]

let compileArgs (defs:GmDefinitions) (env:GmEnvironment) : GmEnvironment =
    let n = List.length defs
    let indexes = List.rev [for i in 0 .. (n-1) -> i]
    let names = List.map fst defs
    (List.zip indexes names) @ (argOffset n env)

type GmCompiler = Expr -> GmEnvironment -> GmCode

let rec compileC (ast : Expr) (env: GmEnvironment) : GmCode =
    match ast with
        | ENum n ->
            [Pushint n]
        | EAp (e1, e2) ->
            (compileC e2 env) @ compileC e1 (argOffset 1 env) @ [Mkap]
        | EVar v ->
            let r = List.tryPick (fun (n, v') ->
                                  if v' = v then Some n else None) env
            match r with
                | Some n ->
                    [Push n]
                | _ ->
                    [Pushglobal v]
        | ELet (recursive, defs, e) ->
            match recursive with
                | true ->
                    compileLetRec compileC defs e env
                | false ->
                    compileLet compileC defs e env
and compileLet (comp: GmCompiler) (defs: GmDefinitions) expr env =
    // inject new definitions into the environment
    let env' = compileArgs defs env
    // compile the definitions using the old environment
    (compileLet' defs env) @
      // compile the expression using the new environment
      (comp expr env') @
      // remove stack items used to construct environment vars
      [Slide (List.length defs)]
and compileLet' defs env =
    match defs with
        | [] ->
            []
        | (name,expr) :: defs' ->
            (compileC expr env) @ compileLet' defs' (argOffset 1 env)
and compileLetRec (comp: GmCompiler) (defs: GmDefinitions) expr env =
    let env' = compileArgs defs env
    let n = List.length defs
    [Alloc n] @ (compileLet'' defs env' (n - 1)) @ (comp expr env') @ [Slide n]
and compileLet'' defs env n =
    match defs with
        | [] ->
            []
        | (name,expr) :: defs' ->
            (compileC expr env) @ [Update n] @ compileLet'' defs' env (n - 1)

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
let compileSc ((name, vars, ast): SC) : GmCompiledSC =
    (name, List.length vars, compileR ast (List.indexed vars))

// (GmHeap, GmGlobals)
let buildInitialHeap (program: CoreProgram) =
    let initialHeap = Map []
    let initialGlobals = Map []
    let compiledPrimitives : GmCompiledSC list = [
        ("+", 2, [Push 1; Eval; Push 1; Eval; Add; Update 2; Pop 2; Unwind]);
        ("-", 2, [Push 1; Eval; Push 1; Eval; Sub; Update 2; Pop 2; Unwind]);
        ("*", 2, [Push 1; Eval; Push 1; Eval; Mul; Update 2; Pop 2; Unwind]);
        ("==",2, [Push 1; Eval; Push 1; Eval; Eq; Update 2; Pop 2; Unwind]);
        (">", 2, [Push 1; Eval; Push 1; Eval; Gt; Update 2; Pop 2; Unwind]);
        ("if",3, [Push 0; Eval; Cond ([Push 1], [Push 2]); Update 3; Pop 3; Unwind])
    ]
    let acc = (initialHeap, initialGlobals)
    let compiled1 = (List.map compileSc program) @ compiledPrimitives
    let (heap, globals) = List.fold allocateSc acc compiled1
    (heap, globals)

let compile (program: CoreProgram) : GmState =
    let initialCode : GmCode =
        [Pushglobal "main"; Eval]
    let (heap, globals) = buildInitialHeap program
    (initialCode, [], [], heap, globals, statInitial)

let getResult (st:GmState) : Node =
    match getStack st with
        | resultAddr :: _ ->
            heapLookup (getHeap st) resultAddr
        | _ ->
            raise (GMError "incorrect VM final state")

[<OneTimeSetUp>]
let Setup () =
    ()

let printTerm term =
    let str = sprintf "%A" term
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

let printState st =
    let code = getCode st
    let stk = getStack st
    let dump = getDump st
    let objs = List.zip stk (List.map (heapLookup (getHeap st)) stk)
    let str = sprintf " code:%A\n dump:%A\n stk:%A\n heap:%A\n*********" code dump stk objs
    NUnit.Framework.TestContext.Progress.WriteLine("{0}", str)

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
    // NUnit.Framework.TestContext.Progress.WriteLine("testK: steps = {0}", getStats finalSt)
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
    // NUnit.Framework.TestContext.Progress.WriteLine("testSKK3: steps = {0}", getStats finalSt)
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
    // NUnit.Framework.TestContext.Progress.WriteLine("testTwiceTwice: steps = {0}", getStats finalSt)
    Assert.AreEqual(NNum 3, getResult finalSt)

[<Test>]
let testCompileArgs0 () =
    let defs = []
    let env = []
    let r = compileArgs defs env
    Assert.AreEqual([], r)

[<Test>]
let testCompileArgs1 () =
    let defs = [("x", ENum 1)]
    let env = []
    let r = compileArgs defs env
    Assert.AreEqual([(0, "x")], r)

[<Test>]
let testCompileArgs2 () =
    let defs = [("x", ENum 1); ("y", EVar "x")]
    let env = []
    let r = compileArgs defs env
    Assert.AreEqual([(1, "x"); (0, "y")], r)

[<Test>]
let testCompileArgs3 () =
    let defs = [("x", ENum 1); ("y", EVar "x")]
    let env = [(5, "z"); (6, "w")]
    let r = compileArgs defs env
    Assert.AreEqual([(1, "x"); (0, "y"); (7, "z"); (8, "w")], r)

[<Test>]
let testLet1 () =
    let coreProg = [
        ("main", [], ELet (false, [("t", ENum 3)], (EVar "t")))
    ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    Assert.AreEqual(NNum 3, getResult finalSt)

[<Test>]
let testLet2 () =
    let coreProg = [
        ("main", [], ELet (false, [("k", ENum 3); ("t", ENum 4)], EVar "t"))
    ]
    let initSt = compile coreProg
    try
        let finalSt = List.last (eval initSt)
        Assert.AreEqual(NNum 4, getResult finalSt)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testLetRecYCombinator () =
    let code = compileSc ("Y", ["f"], ELet (true, [("x", EAp (EVar "f", EVar "x"))], EVar "x"))
    Assert.AreEqual( ("Y", 1, [Alloc 1; Push 0; Push 2; Mkap; Update 0;
                               Push 0; Slide 1; Update 1; Pop 1; Unwind]), code )
[<Test>]
let testCompile1 () =
    let code = compileSc ("X", ["v"; "w"], EAp (EVar "v", EVar "w"))
    // env = [(0, "v"); (1, "w")]
    Assert.AreEqual ( ("X", 2, [Push 1; Push 1; Mkap;
                                Update 2; Pop 2; Unwind]), code )

[<Test>]
let testEval1 () =
    let heap = Map [(0, NNum 1)]
    let stk = [0]
    let dump = []
    let code = [Eval]
    let globals = Map [("0", 0)]
    let stats = 0
    let final = List.last (eval (code, stk, dump, heap, globals, stats))
    Assert.AreEqual (NNum 1, getResult final)

[<Test>]
let testEval2 () =
    let heap = Map [(0, NNum 0);
                    (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]))
                    (2, NAp (1, 0))
                   ]
    let stk = [2]
    let dump = []
    let code = [Eval]
    let globals = Map [("0", 0); ("f", 1)]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, NNum 0);
                         (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]));
                         (2, NInd 0)]
        let stk2 = [0]
        Assert.AreEqual (NNum 0, getResult final)
        Assert.AreEqual (heap2, getHeap final)
        Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testEval3 () =
    let heap = Map [(0, NNum 0);
                    (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]))
                    (2, NAp (1, 0))
                   ]
    let stk = [2; 2]
    let dump = []
    let code = [Eval]
    let globals = Map [("0", 0); ("f", 1)]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, NNum 0);
                         (1, NGlobal (1, [Push 0; Update 1; Pop 1; Unwind]));
                         (2, NInd 0)]
        let stk2 = [0]
        Assert.AreEqual (NNum 0, getResult final)
        Assert.AreEqual (heap2, getHeap final)
        // Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testEval4 () =
    let heap = Map [(0, NGlobal (0, [Pushint 3; Pushint 2; Push 0;
                                     Slide 2; Update 0; Pop 0; Unwind]))]
    let stk = []
    let dump = []
    let code = [Pushglobal "X"; Eval]
    let globals = Map [("X", 0)]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        Assert.AreEqual (NNum 2, getResult (List.last trace))
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testAlloc1 () =
    let heap = Map []
    let globals = Map []
    let stk = []
    let dump = []
    let code = [Alloc 2]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, hNull); (1, hNull)]
        let stk2 = [1; 0]
        Assert.AreEqual (heap2, getHeap final)
        Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testAlloc2 () =
    let heap = Map []
    let globals = Map []
    let stk = [3]
    let dump = []
    let code = [Alloc 2]
    let stats = 0
    try
        let trace = eval (code, stk, dump, heap, globals, stats)
        let final = List.last (trace)
        let heap2 = Map [(0, hNull); (1, hNull)]
        let stk2 = [1; 0; 3]
        Assert.AreEqual (heap2, getHeap final)
        Assert.AreEqual (stk2, getStack final)
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testCompile2 () =
    let code = compileSc ("X", [], ELet (false, [("k", ENum 3); ("t", ENum 2)], EVar "t"))
    // env = [(0, "k"); (1, "t")]
    Assert.AreEqual ( ("X", 0, [Pushint 3; Pushint 2; Push 0; Slide 2; Update 0; Pop 0; Unwind]), code )
    // @3 @2 @2

[<Test>]
[<Ignore("for output")>]
let testCompileLetRec1 () =
    let coreProg = [
        ("main", [], ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t"))
    ]
    let initSt = compile coreProg
    Assert.Ignore()

[<Test>]
[<Ignore("for output")>]
let testCompileSCLetRec1 () =
    let coreProg =
        ("main", [], ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t"))
    printTerm (compileSc coreProg)
    Assert.Ignore()

[<Test>]
let testEvalLetRec1 () =
    let coreProg = [
        ("main", [], ELet (true, [("k", ENum 3); ("t", EVar "k")], EVar "t"))
    ]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 3, res );

[<Test>]
let testEvalAdd1 () =
    let coreProg =
        [("main", [], EAp (EAp (EVar "+", ENum 3), ENum 7))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );

[<Test>]
let testEvalMul1 () =
    let coreProg =
        [("main", [], EAp (EAp (EVar "*", EAp (EAp (EVar "+", ENum 3), ENum 7)), ENum 0))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 0, res );

[<Test>]
let testEvalEq () =
    let coreProg =
        [("main", [], EAp (EAp (EVar "==", ENum 7), ENum 3))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

[<Test>]
let testIf () =
    let coreProg =
        [("main", [], EAp (EAp (EAp (EVar "if", ENum 1), ENum 10), ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );
