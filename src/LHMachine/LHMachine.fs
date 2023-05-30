// For emacs: -*- fsharp -*-

// Here we compile AST into LHMachine abstract VM code.
// Later, that code gets compiled into the TVM code.

// TODO: separate module into two : LHMachine and LHCompiler.

module LHMachine

open System
open System.Collections.Generic
open type LHTypes.Type
open LHExpr

type LHType = LHTypes.Type

open LHTypeInfer

exception GMError of string

// Incomplete pattern matches on this expression.
#nowarn "25"

// This rule will never be matched
#nowarn "26"

type Name = string
type Instruction =
    | Null
    | GetGlob of name: Name
    | SetGlob of name: Name
    | Integer of v: int
    | Function of c:LHCode
    | Fixpoint
    | Apply
    | Push of n: int
    | Pop of n: int
    | Slide of n: int
    | Execute
    | Add | Sub | Mul
    | Equal
    | Greater
    | IfElse of t:LHCode * f:LHCode
    | Pack of tag:int * n:int
    | Record of n:int    // a1 .. an -> { a1, ..., an }
    | Split of n:int
    | Select of n:int    // Take the n-th field of the record
    | UpdateRec of n:int // Update the n-th field of the record
    | Casejump of (int * LHCode) list
    | DumpStk
    | Throw of n:int
    | Alloc of n:int  // Allocate n Null values on the stack
    | Update of i:int // Update the i-th stack value with the one residing on the top
    | Asm of s:string // Assembler inline code
    | FailWith of n:int // raise exception with the given number
and LHCode = Instruction list

// index + variable name
// [(1,"x"); (2,"y"); ...]
// index is needed to know the offset of the variables pointer
// in the stack in case of nested calls
type Environment = (int * Name) list

// AST Expression node
type Expr =
    LHExpr.Expr
type ASTNode =
    LHExpr.ASTNode

type BoundVarDefs =
    (Name * ASTNode) list

// shift all indexes on m places
let argOffset (m:int) (env: Environment) =
    [for (n, v) in env -> (n + m, v)]

let compileArgs (defs:BoundVarDefs) (env:Environment) : Environment =
    let n = List.length defs
    let indexes = List.rev [for i in 0 .. (n-1) -> i]
    let names = List.map fst defs
    (List.zip indexes names) @ (argOffset n env)

// ty is collection of types defined in the actor code
let rec compileWithTypes (ast:ASTNode) (env:Environment) (ty:NodeTypeMap) : LHCode =
    match ast.Expr with
    | EVar v ->
        let r = List.tryPick (fun (n, v') ->
                              if v' = v then Some n else None) env
        match r with
            | Some n ->
                [Push n]
            | None ->
                // a number for the global is assigned in the prelude code
                [GetGlob v]
    | ENum n ->
        [Integer n]
    | ERecord es ->
        let rec compileExprs l env' =
            match l with
            | [] -> []
            | h :: t ->
                (compileWithTypes h env' ty) @
                compileExprs t (argOffset 1 env')
        let es' = List.map snd es
        let n = List.length es' // now we need only values; field names are omitted.
        (compileExprs es' env) @ [Record n]
    | EFunc (argName, body) ->
        let env' = (0, argName) :: (argOffset 1 env)
        // If  it is a function of a single argument, then
        // pack it directly into a lamda abstraction; otherwise,
        // recursively descend one level down with one env index shifted.
        match body.Expr with
        | EFunc (_, _) ->
            compileWithTypes body env' ty
        | _ ->
            [Function (compileWithTypes body env' ty)]
    | ENull ->
        [Null]
    | EAp (e1, e2) ->
        (compileWithTypes e2 env ty) @
        (compileWithTypes e1 (argOffset 1 env) ty) @
        [Apply]
    | EFix f ->
        (compileWithTypes f env ty) @
        [Fixpoint]
    | EEval f ->
        (compileWithTypes f env ty) @
        [Execute]
    | EIf (e0, t, f) ->
        (compileWithTypes e0 env ty) @ [IfElse (compileWithTypes t env ty, compileWithTypes f env ty)]
    | EAdd (e0, e1) ->
        (compileWithTypes e0 env ty) @ (compileWithTypes e1 (argOffset 1 env) ty) @ [Add]
    | ESub (e0, e1) ->
        (compileWithTypes e0 env ty) @ (compileWithTypes e1 (argOffset 1 env) ty) @ [Sub]
    | EMul (e0, e1) ->
        (compileWithTypes e0 env ty) @ (compileWithTypes e1 (argOffset 1 env) ty) @ [Mul]
    | EEq (e0, e1) ->
        (compileWithTypes e0 env ty) @ (compileWithTypes e1 (argOffset 1 env) ty) @ [Equal]
    | EGt (e0, e1) ->
        (compileWithTypes e0 env ty) @ (compileWithTypes e1 (argOffset 1 env) ty) @ [Greater]
    | EPack (tag, arity, args) ->
        List.concat
          (List.map (fun (i, e) -> compileWithTypes e (argOffset i env) ty)
          (List.indexed args)) @
        [Pack (tag, arity)]
    | ECase (e, alts) ->
        (compileWithTypes e env ty) @ [ Casejump (compileAlts alts env ty) ]
    | ELet (name, def, body) ->
        compileLet [(name,def)] body env ty
    | ELetRec (name, def, body) ->
        // compileLetRec [(name,def)] body env ty
        // let rec fact = \n -> n * fact (n-1)
        //  ---> let fact = fixpoint (\fact . \n . n * fact (n - 1))
        // fact 5 --> fixpoint (fact 5)
        let expr = mkAST (ELet (name, mkAST (EFix (mkAST (EFunc (name, def)))), body))
        compileWithTypes expr env ty
    | ESelect (e0, e1) ->
        match (e0.Expr, e1.Expr) with
        | (EVar s, EVar x) ->
            // n = lookup x position in the record definition of e0
            // Currently,the lookup operator '.' is only allowed to be
            // used with records. To compile this expression, we need
            // to find out the index of the "x" field. For that, we need
            // to access type information of e0.
            let stype = ty.[e0.Id]
            // LHTypes.findType s ty     // findType "state" [("state",UserType "State"); ...]
            let ptype =
                match stype with
                | UserType (n, Some ty') ->
                    ty'
                | _ ->
                    stype
            match ptype with
            | PT pts ->
                let n =
                    pts
                    |> List.indexed
                    |> List.find (fun (i,e) -> fst e = x)
                    |> fst
                (compileWithTypes e0 env ty) @ [Select n]
            | _ ->
                failwith "the .dot operator is allowed to be used only on record types"
        | _ ->
            failwith "the . dot operator shall be used only in an explicit form, like:
                      'var.id' , where var is a record-type variable, and id is
                      the name of the record field you want to access"
    | EUpdateRec (e, n, e1) ->
        (compileWithTypes e env ty) @
        (compileWithTypes e1 (argOffset 1 env) ty) @
        [UpdateRec n]
    | EAsm s ->
        [Asm s]
    | EFailWith n ->
        [FailWith n]
    | _ ->
        failwithf "not implemented : %A" (ast.toSExpr())
and compileAlts alts env ty =
    List.map (fun a ->
                 let (tag, names, body) = a
                 let indexed = List.indexed (List.rev names)
                 let env_len = List.length names
                 let env' = indexed @ (argOffset env_len env)
                 (tag, compileAlt env_len body env' ty)
              ) alts
and compileAlt offset expr env ty =
    [Split offset] @ (compileWithTypes expr env ty) @ [Slide offset]
and compileLet (defs: BoundVarDefs) expr env ty =
    // inject new definitions into the environment
    let env' = compileArgs defs env
    let n = List.length defs
    // compile the definitions using the old environment
    (compileLetDefs defs env ty) @
      // compile the expression using the new environment
      (compileWithTypes expr env' ty) @
      // remove local variables after the evaluation
      [Slide n]
and compileLetDefs defs env ty =
    match defs with
        | [] ->
            []
        | (name, expr) :: defs' ->
            (compileWithTypes expr env ty) @ compileLetDefs defs' (argOffset 1 env) ty
// originally, this function was written to do several let-rec compilation at once,
// but later we switched to more managable "let n = expr in" single variable construct,
// nevertheless we didn't change the code, it still support multiple bindings
and compileLetRec defs expr env ty =
    let env' = compileArgs defs env
    let n = List.length defs
    [Alloc n] @ (compileLetRecDefs defs env' n ty) @ (compileWithTypes expr env' ty) @ [Slide n]
and compileLetRecDefs defs env n ty =
    match defs with
        | [] ->
            []
        | (name, node) :: defs' ->
            (compileWithTypes node env ty) @ [Update n] @ compileLetRecDefs defs' env (n - 1) ty

let compile (ast:ASTNode) (env: Environment) : LHCode =
    compileWithTypes ast env (Map [])

let rec instrToTVM (i:Instruction) : string =
    match i with
    | Null -> "NULL"
    | Alloc n -> String.concat " " [for i in [1..n] -> "NULL"]
    | Apply ->  "1 -1 SETCONTARGS"  // inject a single value into cont stack
    | Update i -> "s0 s" + (string i) + " XCHG DROP"
    | GetGlob n -> n + " GETGLOB"
    | SetGlob n -> n + " SETGLOB"
    | Integer n -> (string n) + " INT"
    | Push n -> "s" + (string n) + " PUSH"
    | Pop n -> "s" + (string n) + " POP"
    | Slide n -> String.concat " " [for i in [1..n] -> "NIP"]
    | Function b -> "<{ " + (compileToTVM b) + " }> PUSHCONT"
    | Fixpoint -> " 2 GETGLOB 1 1 CALLXARGS"
    | Execute -> " 0 1 CALLXARGS" // execute a saturated function
    | Add -> "ADD"
    | Sub -> "SUB"
    | Mul -> "MUL"
    | Equal -> "EQUAL"
    | Greater -> "GREATER"
    | IfElse (t, f) ->
        "<{ " + (compileToTVM t) + " }> PUSHCONT " +
        "<{ " + (compileToTVM f) + " }> PUSHCONT IFELSE"
    | DumpStk -> "DUMPSTK"
    | Throw n -> (string n) + " THROW"
    | Pack (tag, arity) ->
        (string arity) + " TUPLE" +
        " " + (string tag) + " INT" +
        " SWAP" +
        " 2 TUPLE"
    | Split n when n < 16 ->
        " SECOND" + " " +
        (string n) + " UNTUPLE"
    | Select n when n < 16 ->
        " SECOND" + " " +
        (string n) + " INDEX"
    | Record n when n < 16 ->
        (string n) + " TUPLE"
    | UpdateRec n when n < 16 ->
        " SWAP" +      // x t
        " 2 UNTUPLE" + // x tag args
        " ROT " +      // tag args x
        (string n) + " SETINDEX" +
        " 2 TUPLE"
    | Casejump l ->
        let rec compileCasejumpSelector l =
            match l with
            | [] ->
                "10 THROW " // proper case selector not found (shall not happen)
            | (tag, code) :: t ->
                "DUP " + (string tag) + " INT EQUAL " +
                "<{ DROP " + compileToTVM code + " }> PUSHCONT IFJMP " +
                compileCasejumpSelector t
        let l' = compileCasejumpSelector l
        "DUP 0 INDEX <{ " + l' + " }> " + " PUSHCONT EXECUTE"
    | Asm s ->
        s
    | FailWith n ->
        " " + (string n) + " THROW"
    | _ ->
        failwith (sprintf "unimplemented instruction %A"  i)
and compileToTVM (code:LHCode) : string =
    code
    |> List.map instrToTVM
    |> String.concat " "
and mkFiftCell (body: string) : string =
    "<{ " + body + "}>c "

let rec astReducer (ast:ASTNode) (red: ASTNode -> ASTNode) : ASTNode =
    match ast.Expr with
    // leaf nodes
    | EVar _
    | ENull
    | EStr _
    | EFailWith _
    | ENum _ ->
        ast
    | EFunc (arg, body) ->
        let body' = astReducer body red
        if body'.toSExpr () <> body.toSExpr () then mkAST (EFunc (arg, body'))
        else ast
    | ELet (name, bind, body)
    | ELetRec (name, bind, body) ->
        let bind' = astReducer bind red
        let body' = astReducer body red
        if bind'.toSExpr () <> bind.toSExpr () || (body'.toSExpr () <> body.toSExpr ()) then
            match ast.Expr with
            | ELet _ ->
                mkAST (ELet (name, bind', body'))
            | ELetRec _ ->
                mkAST (ELetRec (name, bind', body'))
        else ast
    | EIf (e0, e1, e2) ->
        let e0' = astReducer e0 red
        let e1' = astReducer e1 red
        let e2' = astReducer e2 red
        if e0'.toSExpr () <> e0.toSExpr () ||
           e1'.toSExpr () <> e1.toSExpr () ||
           e2'.toSExpr () <> e2.toSExpr () then
              mkAST (EIf (e0', e1', e2'))
        else ast
    | EAp (e0, e1)
    | EAdd (e0, e1)
    | ESub (e0, e1)
    | EMul (e0, e1)
    | EGt (e0, e1)
    | EEq (e0, e1)
    | ESelect (e0, e1) ->
        let e0' = astReducer e0 red
        let e1' = astReducer e1 red
        if e0'.toSExpr () <> e0.toSExpr () ||
           e1'.toSExpr () <> e1.toSExpr () then
            match ast.Expr with
            | EAp _ -> mkAST (EAp (e0', e1'))
            | EAdd _ -> mkAST (EAdd (e0', e1'))
            | ESub _ -> mkAST (ESub (e0', e1'))
            | EMul _ -> mkAST (EMul (e0', e1'))
            | EGt _ -> mkAST (EGt (e0', e1'))
            | EEq _ -> mkAST (EEq (e0', e1'))
            | ESelect _ -> mkAST (ESelect (e0', e1'))
        else ast
    | ERecord es ->
        let node' =
          es
          |> List.map (fun (name, e) -> (name, astReducer e red))
          |> ERecord
          |> mkAST
        if node'.toSExpr () <> ast.toSExpr () then node'
        else ast
    | _ ->
        failwithf "unrecognised node %A" ast.Expr
    |> red

// eta reduction step:
// (\x -> f x) ==> f
let rec etaStep (node:ASTNode) : ASTNode =
    match node.Expr with
    | EFunc (arg, body) ->
        match body.Expr with
        | EAp (f, f_arg) ->
            match f_arg.Expr with
            | EVar arg1 when arg1 = arg ->
                etaStep f
            | _ ->
                node
        | _ ->
            let red = etaStep body
            if red = body then node
            else etaStep (mkAST (EFunc (arg, red)))
    | _ ->
        node

let etaRedex node =
    astReducer node etaStep

// Return a list of free (unbound) variables in expression 'node'
let rec freeVars (expr:Expr) : string list =
    match expr with
    | EVar x -> List.singleton x
    | EFunc (y, body) ->
        freeVars body.Expr |> List.except [y]
    | EAp (e1, e2)
    | EGt (e1, e2)
    | EAdd (e1, e2)
    | ESub (e1, e2)
    | EMul (e1, e2) ->
        (freeVars e1.Expr) @ (freeVars e2.Expr)
    | ELet (x, bind, body) ->
        (freeVars bind.Expr) @ (freeVars body.Expr)
    | ELetRec (x, bind, body) ->
        (freeVars bind.Expr) @ (freeVars body.Expr)
    | ENum _ -> []
    | EIf (e1, e2, e3) ->
        (freeVars e1.Expr) @ (freeVars e2.Expr) @ (freeVars e3.Expr)
    | _ ->
        failwithf "freeVars for %A not implemented" expr

// global counter for generating unique variable names
let private nameId = ref 0

// Substitute a free variable 'x' for the term y in the 'node'
let rec substFreeVar (x:string) (y:Expr) (node:ASTNode) : ASTNode =
    let newVarName () =
        let id = !nameId
        nameId := id + 1 ;
        "z" + (string id)
    match node.Expr with
    | EVar x' ->
        if x' = x then mkAST y
        else node
    | ENum _
    | ENull ->
        node
    | EGt (e0, e1)
    | ESub (e0, e1)
    | EMul (e0, e1)
    | EAdd (e0, e1)
    | EEq (e0, e1)
    | EAp (e0, e1) ->
        let e0' = substFreeVar x y e0
        let e1' = substFreeVar x y e1
        mkAST ( match node.Expr with
                | EGt _ -> EGt (e0', e1')
                | EEq _ -> EEq (e0', e1')
                | ESub _ -> ESub (e0', e1')
                | EMul _ -> EMul (e0', e1')
                | EAdd _ -> EAdd (e0', e1')
                | EAp _ -> EAp (e0', e1')
              )
    | EIf (e0, e1, e2) ->
        mkAST (EIf (substFreeVar x y e0, substFreeVar x y e1, substFreeVar x y e2))
    | EFunc (x', body) when x' = x ->
        node
    | EFunc (name, body) ->  // here name <> x
        let yFreeVars = freeVars y
        if List.contains name yFreeVars then
            let z = newVarName ()
            let newBody = substFreeVar name (EVar z) body
            mkAST (EFunc (z, substFreeVar x y newBody))
        else
            mkAST (EFunc (name, substFreeVar x y body))
    | ELet (arg, bind, body) ->
        mkAST (ELet (arg, substFreeVar x y bind, substFreeVar x y body))
    | ELetRec (arg, bind, body) ->
        mkAST (ELetRec (arg, substFreeVar x y bind, substFreeVar x y body))
    | ERecord es ->
        let es' = List.map (fun (name, term) -> (name, substFreeVar x y term)) es
        mkAST (ERecord es')
    | ESelect (e0, e1) ->
        mkAST (ESelect ((substFreeVar x y e0), e1))
    | EFailWith _ ->
        node
    | _ ->
        failwithf "substFreeVar not implemented for %A" node.Expr

let rec betaRedexStep (node:ASTNode) : ASTNode =
    match node.Expr with
    | ELetRec (x, bind, body) ->
        mkAST (ELetRec (x, betaRedexStep bind, betaRedexStep body))
    | ELet (x, bind, body) ->
        substFreeVar x bind.Expr body
    | EAp (e0, arg) ->
        match e0.Expr with
        | EFunc (x, body) ->
            substFreeVar x arg.Expr body
        | term -> // EAp (EAp (...), arg)
            let node' = betaRedexStep e0
            if term <> node'.Expr then
                mkAST (EAp (node', arg))
            else
                node
    | EAdd (e0, e1)
    | EMul (e0, e1)
    | ESub (e0, e1)
    | EGt (e0, e1) ->
        let e0' = betaRedexStep e0
        let e1' = betaRedexStep e1
        if e0'.Expr <> e0.Expr || e1'.Expr <> e1.Expr then
            match node.Expr with
            | EAdd _ -> mkAST (EAdd (e0', e1'))
            | ESub _ -> mkAST (ESub (e0', e1'))
            | EMul _ -> mkAST (EMul (e0', e1'))
            | EGt _ -> mkAST (EGt (e0', e1'))
        else
            node
    | EIf (e0, e1, e2) ->
        let e0' = betaRedexStep e0
        let e1' = betaRedexStep e1
        let e2' = betaRedexStep e2
        if e0'.Expr <> e0.Expr ||
           e1'.Expr <> e1.Expr ||
           e2'.Expr <> e2.Expr then
            mkAST (EIf (e0', e1', e2'))
        else
            node
    | EVar _
    | EFunc _
    | ENum _ ->
        node
    | ERecord vs ->  // record instance: [(name,expr)]
        let vs' =
            vs
            |> List.map ( fun (n, e) -> (n, betaRedexStep e) )
        mkAST (ERecord vs')
    | ESelect (ASTNode (_, ERecord vs), ASTNode (_, EVar n)) ->
        Map.ofList vs
        |> Map.tryFind n
        |> function
           | None ->
               failwithf "field %A not found in the record %A" n (node.toSExpr())
           | Some v ->
               mkAST v.Expr
    | _ ->
        failwithf "Redex for expr %A not defined" node.Expr

let rec betaRedexFullDebug node debug =
    let node' = betaRedexStep node
    if node'.toSExpr () <> node.toSExpr () then
        if debug then
            printfn "*** %A" (node'.toSExpr ())
        betaRedexFullDebug node' debug
    else node

// Do redexes until progress stops. We assume that fixpoints
// do not get expanded.
let rec betaRedexFull node =
    betaRedexFullDebug node false

let rec arithSimplRedex node =
    let arithSimpl (node : ASTNode) =
        match (node.toSExpr ()) with
        | SAdd (SNum x, SNum y) ->
            mkAST (ENum (x + y))
        | SSub (SNum x, SNum y) ->
            mkAST (ENum (x - y))
        | SMul (SNum x, SNum y) ->
            mkAST (ENum (x * y))
        | SGt (SNum x, SNum y) ->
            mkAST (ENum (if x > y then -1 else 0))
        | SEq (SNum x, SNum y) ->
            mkAST (ENum (if x = y then -1 else 0))
        | _ ->
            node
    in astReducer node arithSimpl


// Here we substitute 'false' letrecs (with no recursion in them),
// for ordinary let expressions; this step has to be done before
// type inference.
let rec letrecRedex node =
    let letrecRedexStep (node:ASTNode) =
        match node.Expr with
        | ELetRec (name, bind, body) ->
            if not (List.contains name (freeVars bind.Expr)) then
                mkAST (ELet (name, bind, body))
            else node
        | _ ->
            node
    in astReducer node letrecRedexStep

let rec insertEval (ast:ASTNode) (ty:Map<int,LHType>) : ASTNode =
    let rec insertEvalInner (node:ASTNode) : ASTNode =
        match node.Expr with
        | EAp (e1, e2) ->
            let t =
                match (Map.tryFind node.Id ty) with
                | Some v -> v
                | None -> failwithf "failed to find type for node %A, expression: %A" node.Id (ast.toSExpr ())
            if (t = LHTypes.Int 256 ||
                t = LHTypes.Bool ||
                t = LHTypes.String) then
                mkAST (EEval node)
            else
                node
        | _ ->
            node
    in astReducer ast insertEvalInner

let printDict d =
    printfn "%A" (Map.toList d)

// Please keep in mind that there is a hard limit of 15 arguments for
// recursive functions.
let fixpointImpl = "
 <{
   <{
     DEPTH
     -2 ADDCONST
     TUPLEVAR
     s2 PUSH
     s2 PUSH
     DUP
     2 -1 SETCONTARGS
     s0 s2 XCHG
     DROP
     s1 s2 XCHG
     15 EXPLODE
     ROLLX
     DEPTH
     DEC
     TRUE
     CALLXVARARGS
   }> PUSHCONT
   DUP
   2 -1 SETCONTARGS
 }> PUSHCONT
 2 SETGLOB"  // fixpoint operator is stored in global 2

let tprintf str debug =
    fun x ->
        if debug then printfn str else () |> ignore
        x

let compileIntoFiftDebug ast initialTypes debug : string =
    let ast' =
        ast
        |> tprintf "Making LetRec reductions..." debug
        |> letrecRedex
        |> tprintf "Making ETA reductions..." debug
        |> etaRedex
        |> tprintf "Making BETA reductions..." debug
        |> (fun n -> betaRedexFullDebug n debug)
        |> tprintf "Making Arith reductions..." debug
        |> arithSimplRedex
    if debug then
        printfn "AST after beta and eta redex : %A" (ast'.toSExpr ())
    if debug then
        printfn "Running type inference..."
    let (ty, (oldMap, newMap)) =
        LHTypeInfer.typeInferenceDebug (LHTypeInfer.TypeEnv.ofProgramTypes initialTypes) ast' debug
    if debug then
        printfn "Inserting Eval nodes..."
    let ast'' = insertEval ast' newMap // AST with EEval nodes inserted into the right places
    let hasFixpoint = true // ast''.hasNode (function | SFix _ -> true | _ -> false)
    if debug then
        printfn "Compiling reduced AST into assembly..."
    let ir = compileWithTypes ast'' [] newMap
    if debug then
        printfn "Expr AST:\n%A" ast ;
        printfn "SExpr AST:\n%O" (ast''.toSExpr()) ;
        printfn "Types:\n%A" (Map.toList newMap) ;
        printfn "IR:\n%A" ir
    List.singleton "\"Asm.fif\" include" @
    List.singleton "<{ " @
    (if hasFixpoint then [fixpointImpl] else []) @
    List.singleton   (compileToTVM ir) @
    List.singleton " }>s 1000000 gasrunvmcode drop .dump cr .dump cr"
    |> String.concat "\n"

let compileIntoFift ast =
    compileIntoFiftDebug ast [] false

let compileWithInitialTypesDebug ast types debug =
    compileIntoFiftDebug ast types debug

let compileWithInitialTypes ast types =
    compileWithInitialTypesDebug ast types false
