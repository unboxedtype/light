module GMachine

open NUnit.Framework
open System
open System.Collections.Generic

exception GMError of string

// Incomplete pattern matches on this expression.
#nowarn "25"

// This rule will never be matched
#nowarn "26"

type Name = string
type Instruction =
    // Pushglobal f:Name
    // Extract the address of function name from the globals
    // and put it on the stack; if the function with the given
    // name is not found, raise exception.
    | Pushglobal of name: Name

    // Pushint v:int
    // Allocate a node for the integer on the heap and put the
    // address of that node on the stack;
    | Pushint of v: int

    // Push n:int
    // Put the n-th element of the stack on top of the stack;
    // 0 denotes the current top value of the stack.
    | Push of n: int

    // Pop n:int
    // Remove n consecutive elements from the stack
    | Pop of n: int

    // Mkap
    // Allocate a node for function application on the heap and
    // put the address of that node on the stack
    | Mkap

    // Update n:int
    // Change the node pointed by the n-th + 1 element of the stack
    // to the Indirection node pointing to the node with the address
    // located on top of the stack.
    | Update of n: int

    // Slide n:int
    // Remove n elements from the stack, starting from the second
    // element of the stack, i.e. leaving the top stack element inplace.
    | Slide of n: int

    // Alloc n:int
    // Allocate n dummy nodes on the heap and return put their addresses
    // on the stack
    | Alloc of n: int

    // Unwind
    // If the current top stack element is:
    //  - a value, i.e. a number or a saturated constructor,
    //    then switch to the frame (instructions,stack pair) located on top of the dump.
    //  - an Indirection node, then put the indirection
    //    address on the stack and Unwind further
    //  - a global function, then put the parameters
    //    of the function onto the stack and execute the function instructions.
    //    If there are not enough arguments on the stack (partial application), then
    //    switch to dump code/stack pair
    //  - an application node, then put the function address (i.e. first element of the application)
    //    on the stack and Unwind further
    | Unwind

    // Eval
    // Save the current code and stack (without the top element) to the dump,
    // and Unwind with current top stack element.
    | Eval

    // Add, Sub, Mul, Div
    // lookup arguments on the heap and do the corresponding arithmetic
    // operation, placing the boxed result on the stack
    | Add | Sub | Mul | Div

    // same for logical operations
    | Equal | Greater

    // Cond (t, f)
    // If the top stack element evaluates to True, transfer control
    // to the t branch; else to the f branch
    | Cond of t:GmCode * f:GmCode

    // Pack (tag, n)
    // Put the boxed constructor object onto the stack
    | Pack of tag:int * n:int

    // Casejump [(int, GmCode)]
    // Extract the constructor object's tag and transfer
    // control the code given in the corresponding case branch
    | Casejump of (int * GmCode) list

    // Split (n:int)
    // Deconstruct the constructor object located on the stack,
    // having n arguments. All arguments are placed onto the stack.
    | Split of n:int
and
    GmCode = Instruction list

type Addr = int
type GmStack = Addr list
// Expression node (when computing, not AST)
type Node =
    | NNum of v: int
    | NAp of f: Addr * a: Addr // f(a)
    | NGlobal of args: int * code: GmCode
    | NInd of v: Addr  // indirection node
    // data type constructor with n params
    | NConstr of int * Addr list

// To be used in Node serialization purposes
// Denotes a constructor tag
type NodeTags =
    | NNum = 0
    | NAp = 1
    | NGlobal = 2
    | NInd = 3
    | NConstr = 4

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

let heapLookup (heap:GmHeap) (key:Addr) : Node =
    match Map.tryFind key heap with
        | Some v ->
            v
        | None ->
            let msg = sprintf "key %A not found in the map" key
            raise (GMError msg)

let heapUpdate (heap:GmHeap) (key:Addr) (v:Node) =
    Map.add key v heap

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
                        putCode code (putDump dump' (putStack (a :: stack) state))
                    | NAp (a1, a2) ->
                        putCode [Unwind] (putStack (a1 :: a :: as') state)
                    | NGlobal (n, c) ->
                        let k = List.length as'
                        if k < n then // number of passed arguments is less than the arity
                            let ((code, stack) :: dump') = getDump state
                            let stack' =
                                if k > 0 then
                                    let ak = List.item (k - 1) as'
                                    ak :: stack
                                else
                                    stack
                            putCode code (putStack stack' (putDump dump' state))
                        else
                            putCode c (putStack (rearrange n heap (a :: as')) state)
                    | NInd a0 ->
                        putCode [Unwind] (putStack (a0 :: as') state)
                    | NConstr (_, _) ->
                        let dump = getDump state
                        failIf (List.length dump = 0) "Unwind with an empty dump"
                        let (code, stack) = List.head (getDump state)
                        let dump' = List.tail dump
                        putCode code (putDump dump' (putStack (a :: stack) state))
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
let div state =
    binop (fun a b -> a / b) state

let eq state =
    cmpop (fun a b -> a = b) state
let gt state =
    cmpop (fun a b -> a > b) state

let cond i1 i2 state =
    let (a :: s') = getStack state
    let heap = getHeap state
    match (heapLookup heap a) with
        | NNum a when a = 1 ->
            putStack s' (putCode (i1 @ (getCode state)) state)
        | NNum a when a = 0 ->
            putStack s' (putCode (i2 @ (getCode state)) state)
        | _ ->
            raise (GMError "incorrect conditional variable")

let pack tag n state =
    let args = List.take n (getStack state)
    let (heap', a) = heapAlloc (getHeap state) (NConstr (tag, args))
    let s' = List.skip n (getStack state)
    putHeap heap' (putStack (a::s') state)

let casejump cases state =
    let (a :: stack) = getStack state
    let code = getCode state
    let heap = getHeap state
    match (heapLookup heap a) with
        | NConstr (tag, args) ->
            let cs = List.pick (fun (tag', code') ->
                                if (tag' = tag) then (Some code') else None
                                ) cases
            putCode (cs @ code) state
        | _ ->
            raise (GMError "no constructor object found on the heap")

let split n state =
    let (a :: stack) = getStack state
    let heap = getHeap state
    match (heapLookup heap a) with
        | NConstr (tag, args) ->
            putStack (args @ stack) state
        | _ ->
            raise (GMError "no constructor object found on the heap")

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
        | Div ->
            div
        | Equal ->
            eq
        | Greater ->
            gt
        | Pack (tag, n) ->
            pack tag n
        | Casejump cases ->
            casejump cases
        | Split n ->
            split n
        | _ ->
            raise (GMError "not implemented")
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
    | ELet of isRec:bool * defs:BoundVarDefs * body:Expr
    | EIf of e0:Expr * e1:Expr * e2:Expr
    | EAdd of e0:Expr * e1:Expr
    | ESub of e0:Expr * e1:Expr
    | EMul of e0:Expr * e1:Expr
    | EEq of e0:Expr * e1:Expr
    | EGt of e0:Expr * e1:Expr
    | EDiv of e0:Expr * e1:Expr
    | ECase of c:Expr * cs:CaseAlt list
    | EPack of tag:int * arity:int * args:Expr list
and CaseAlt = int * (Name list) * Expr   // case (tag:0) (vars: ["x","y"]) -> x + y
and BoundVarDefs = (Name * Expr) list


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
// [(1,"x"); (2,"y"); ...]
// index is needed to know the offset of the variables pointer
    // in the stack
type GmEnvironment = (int * Name) list

// shift all indexes on m places
let argOffset (m:int) (env: GmEnvironment) =
    [for (n, v) in env -> (n + m, v)]

let compileArgs (defs:BoundVarDefs) (env:GmEnvironment) : GmEnvironment =
    let n = List.length defs
    let indexes = List.rev [for i in 0 .. (n-1) -> i]
    let names = List.map fst defs
    (List.zip indexes names) @ (argOffset n env)

type GmCompiler = Expr -> GmEnvironment -> GmCode

// compileE corresponds to 'strict' context compilation scheme;
// If expression needs not be evaluated strictly, then
// postpone it to the lazy compilation scheme compileC
let rec compileE (ast : Expr) (env: GmEnvironment) : GmCode =
    match ast with
        | ENum n ->
            [Pushint n]
        | ELet (recursive, defs, e) ->
            match recursive with
                | true ->
                    compileLetRec compileE defs e env
                | false ->
                    compileLet compileE defs e env
        | EAdd (e1, e2) ->
            (compileE e2 env) @ (compileE e1 (argOffset 1 env)) @ [Add]
        | ESub (e1, e2) ->
            (compileE e2 env) @ (compileE e1 (argOffset 1 env)) @ [Sub]
        | EMul (e1, e2) ->
            (compileE e2 env) @ (compileE e1 (argOffset 1 env)) @ [Mul]
        | EEq (e1, e2) ->
            (compileE e2 env) @ (compileE e1 (argOffset 1 env)) @ [Equal]
        | EGt (e1, e2) ->
            (compileE e2 env) @ (compileE e1 (argOffset 1 env)) @ [Greater]
        | EDiv (e1, e2) ->
            (compileE e2 env) @ (compileE e1 (argOffset 1 env)) @ [Div]
        | EIf (e0, e1, e2) ->
            (compileE e0 env) @ [Cond(compileE e1 env, compileE e2 env)]
        | ECase (c, alts) ->
            (compileE c env) @ [Casejump(compileAlts alts env)]
        | EPack (tag, n, args) ->
            List.concat (List.map (fun (i, e) -> compileC e (argOffset i env))
               (List.indexed (List.rev args))) @ [Pack (tag, n)]
        | _ ->
            (compileC ast env) @ [Eval]
and compileC (ast : Expr) (env: GmEnvironment) : GmCode =
    match ast with
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
        | _ ->
            compileE ast env
            // raise (GMError "unexpected term")
and compileLet (comp: GmCompiler) (defs: BoundVarDefs) expr env =
    // inject new definitions into the environment
    let env' = compileArgs defs env
    let n = List.length defs
    // compile the definitions using the old environment
    (compileLet' defs env) @
      // compile the expression using the new environment
      (comp expr env') @
      // remove stack items used to construct environment vars
      [Slide n]
and compileLet' defs env =
    match defs with
        | [] ->
            []
        | (name,expr) :: defs' ->
            (compileC expr env) @ compileLet' defs' (argOffset 1 env)
and compileLetRec (comp: GmCompiler) (defs: BoundVarDefs) expr env =
    let env' = compileArgs defs env
    let n = List.length defs
    [Alloc n] @ (compileLet'' defs env' (n - 1)) @ (comp expr env') @ [Slide n]
and compileLet'' defs env n =
    match defs with
        | [] ->
            []
        | (name,expr) :: defs' ->
            (compileC expr env) @ [Update n] @ compileLet'' defs' env (n - 1)
and compileAlts alts env =
    List.map (fun a ->
                 let (tag, names, body) = a
                 let indexed = List.indexed names
                 let env_len = List.length names
                 let env' = indexed @ (argOffset env_len env)
                 (tag, compileE' env_len body env')
              ) alts
and compileE' offset expr env =
    [Split offset] @ (compileE expr env) @ [Slide offset]

// ast env -> Instruction list
let compileR ast env =
    let n = List.length env
    compileE ast env @ [Update n; Pop n; Unwind]

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
    let compiledPrimitives : GmCompiledSC list = []
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
    let code = compileSc ("K1", ["x"; "y"], (EVar "x"))
    Assert.AreEqual( ("K1", 2, [Push 0; Eval; Update 2; Pop 2; Unwind]), code );

[<Test>]
let compileScFTest () =
    let code = compileSc ("F", ["x"; "y"], (EAp (EVar "z", EVar "x")))
    Assert.AreEqual( ("F", 2, [Push 0; Pushglobal "z"; Mkap; Eval; Update 2; Pop 2; Unwind]), code );

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
    let finalSt = List.last (eval initSt)
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
    let finalSt = List.last (eval initSt)
    Assert.AreEqual( NNum 3, getResult finalSt )

[<Test>]
[<Ignore("partial application case")>]
let testTwiceTwice () =
    let coreProg = [
        // twice f x = f (f x)
        ("twice", ["f"; "x"], EAp (EVar "f", EAp (EVar "f", EVar "x")))
        // id x = x
        ("id", ["x"], EVar "x");
         // main = twice twice id 3
        ("main", [], EAp (EVar "twice", EAp (EVar "twice", EAp (EVar "id", ENum 3))))
    ]
    let initSt = compile coreProg
    let rec repeat f n st =
        if n = 0 then st else repeat f (n-1) (f st)
    // List.map printState (List.map (fun n -> repeat step n initSt) [0..20])
    // Assert.Fail()
    let finalSt = List.last (eval initSt)
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
                               Push 0; Eval; Slide 1; Update 1; Pop 1; Unwind]), code )
[<Test>]
let testCompile1 () =
    let code = compileSc ("X", ["v"; "w"], EAp (EVar "v", EVar "w"))
    // env = [(0, "v"); (1, "w")]
    Assert.AreEqual ( ("X", 2, [Push 1; Push 1; Mkap; Eval;
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
    Assert.AreEqual ( ("X", 0, [Pushint 3; Pushint 2; Push 0; Eval; Slide 2; Update 0; Pop 0; Unwind]), code )
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
   // printTerm (compileSc coreProg)
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
        [("main", [], EAdd (ENum 3, ENum 7))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );

[<Test>]
let testEvalMul1 () =
    let coreProg =
        [("main", [], EMul (EAdd (ENum 3, ENum 7), ENum 0))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 0, res );

[<Test>]
let testEvalEq () =
    let coreProg =
        [("main", [], EEq (ENum 7, ENum 3))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

[<Test>]
let testIfTrue () =
    let coreProg =
        [("main", [], EIf (ENum 1, ENum 10, ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );

[<Test>]
let testIfFalse () =
    let coreProg =
        [("main", [], EIf (ENum 0, ENum 10, ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 20, res );

[<Test>]
let testSub () =
    let coreProg =
        [("main", [], ESub (ENum 10, ENum 1))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 9, res );

[<Test>]
let testEqFalse () =
    let coreProg =
        [("main", [], EEq (ENum 10, ENum 1))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

let testEqTrue () =
    let coreProg =
        [("main", [], EEq (ENum 10, ENum 10))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NTrue, res );

[<Test>]
let testMul () =
    let coreProg =
        [("main", [], EMul (ENum 10, ENum 20))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 200, res );

[<Test>]
let testGtTrue () =
    let coreProg =
        [("main", [], EGt (ENum 10, ENum 1))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NTrue, res );

[<Test>]
let testGtFalse () =
    let coreProg =
        [("main", [], EGt (ENum 1, ENum 10))]
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NFalse, res );

[<Test>]
let testRec1 () =
    let coreProg =
        [("rec", ["n"], EIf (EGt (EVar "n", ENum 1), EAp (EVar "rec", ESub (EVar "n", ENum 1)), ENum 20))
         ("main", [], EAp (EVar "rec", ENum 10))]
    try
      let initSt = compile coreProg
      let finalSt = List.last (eval initSt)
      let res = getResult finalSt
      Assert.AreEqual( NNum 20, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testRec2 () =
    let coreProg =
        // rec n m = if (n > 1) then (rec (n-1) n) else m
        // rec 10 3 = rec 9 10  = rec 8 9 = rec 7 8 = rec 6 7 = ...
        //  ... = rec 1 2 = 2
        [("rec", ["n"; "m"],
          EIf (
            EGt (EVar "n", ENum 1),
            EAp (EAp (EVar "rec", ESub (EVar "n", ENum 1)), EVar "n"),
            EVar "m"
            )
          )
         ("main", [], EAp (EAp (EVar "rec", ENum 10), ENum 3))]
    try
      let initSt = compile coreProg
      // printTerm initSt
      let finalSt = List.last (eval initSt)
      let res = getResult finalSt
      Assert.AreEqual( NNum 2, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testSumRec () =
    let coreProg =
        // sum n acc = if (n > 0) then (sum (n-1) (acc+n)) else acc
        // sum 4 0 = sum 3 4 = sum 2 7 = sum 1 9 = sum 0 10 = 10
        [("sum", ["n"; "acc"],
          EIf (
            EGt (EVar "n", ENum 0),
            EAp (EAp (EVar "sum", ESub (EVar "n", ENum 1)), EAdd(EVar "acc", EVar "n")),
            EVar "acc"
            )
          );
         ("main", [], EAp (EAp (EVar "sum", ENum 4), ENum 0))
         ]
    try
      let initSt = compile coreProg
      // List.map printTerm (eval initSt) |> ignore
      let finalSt = List.last (eval initSt)
      let res = getResult finalSt
      // printTerm (getStats finalSt)
      Assert.AreEqual( NNum 10, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testMaxFunction () =
    let coreProg =
        [("max", ["n"; "m"], EIf (EGt (EVar "n", EVar "m"), EVar "n", EVar "m"));
         ("main", [], EAp (EAp (EVar "max", ENum 5), ENum 6))]
    try
      let initSt = compile coreProg
      let res = getResult (List.last (eval initSt))
      Assert.AreEqual( NNum 6, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testFact () =
    let coreProg =
        // fact n = if n == 0 then 1 else n * fact(n-1)
        // main = fact 5
        [("fact", ["n"],
          EIf (EEq (EVar "n", ENum 0),
               ENum 1, // true branch
               EMul (EVar "n", EAp (EVar "fact", ESub (EVar "n", ENum 1)))) // else branch
          )
         ("main", [], EAp (EVar "fact", ENum 5))]
    try
      let initSt = compile coreProg
      // List.map printTerm (eval initSt) |> ignore
      let res = getResult (List.last (eval initSt))
      Assert.AreEqual( NNum 120, res );
    with
        | GMError s ->
            Assert.Fail(s)

[<Test>]
let testConstr0 () =
    let coreProg =
        [("main", [], EPack (0, 0, []))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    Assert.AreEqual( NConstr (0, []), res );

[<Test>]
let testConstr1 () =
    let coreProg =
        [("main", [], EPack (0, 2, [ENum 1; ENum 2]))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (0, [2; 1]), res );
    Assert.AreEqual( heapLookup heap 2, NNum 1 );
    Assert.AreEqual( heapLookup heap 1, NNum 2 );

[<Test>]
let testConstr2 () =
    let coreProg =
        [("main", [], EPack (0, 2, [EAdd (ENum 1, ENum 2); ESub (ENum 10, ENum 5)]))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (0, [6; 3]), res );
    Assert.AreEqual( heapLookup heap 6, NNum 3 );
    Assert.AreEqual( heapLookup heap 3, NNum 5 );

[<Test>]
let testConstr3 () =
    // nested constructors
    let coreProg =
        [("main", [], EPack (0, 1, [EPack (1, 0, [])]))]
    // printTerm (compile coreProg)
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (0, [1]), res );
    Assert.AreEqual( heapLookup heap 1, NConstr (1, []) );

[<Test>]
let testCase1 () =
    // nested constructors
    let coreProg =
        [("some", [], EPack (0, 1, [EPack (1, 0, [])]));
         ("main", [], ECase (EVar "some", [(0, ["x"], EVar "x")]))
         ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NConstr (1, []), res );

[<Test>]
let testCase2 () =
    // nested constructors
    let coreProg =
        [("some", [], EPack (1, 2, [ENum 1; ENum 2]));
         ("main", [], ECase (EVar "some", [(0, ["x"], EVar "x");
                                           (1, ["x"; "y"], EAdd (EVar "x", EVar "y"))
                                           ]
                             )
          )
         ]
    let initSt = compile coreProg
    let finalSt = List.last (eval initSt)
    let res = getResult finalSt
    let heap = getHeap finalSt
    Assert.AreEqual( NNum 3, res );

[<Test>]
[<Ignore("bug")>]
let testLazyDiv0 () =
    let coreProg =
        [("main", [], EAp (EAp (EVar "K", ENum 1), EDiv(ENum 1, ENum 0)))]
    printTerm (compile coreProg)
    let initSt = compile coreProg
    let res = getResult (List.last (eval initSt))
    Assert.AreEqual( NNum 10, res );
