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
let rec compileWithTypes (ast:ASTNode) (env:Environment) (ty:LHTypes.ProgramTypes) : LHCode =
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
        let n = List.length es
        (compileExprs es env) @ [Record n]
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
            let stype = LHTypes.findType s ty     // findType "state" [("state",UserType "State"); ...]
            let ptype =
                match stype with
                | UserType (n, ty') ->
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
    | _ ->
        failwith "not implemented"
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
    compileWithTypes ast env []

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
    | _ ->
        failwith (sprintf "unimplemented instruction %A"  i)
and compileToTVM (code:LHCode) : string =
    code
    |> List.map instrToTVM
    |> String.concat " "
and mkFiftCell (body: string) : string =
    "<{ " + body + "}>c "

let rec astReducer (ast:ASTNode) (red: ASTNode -> ASTNode) : ASTNode =
    let ast' = red ast
    match ast'.Expr with
    | EFunc (arg, body) ->
        mkAST (EFunc (arg, astReducer body red))
    | ELet (name, bind, body) ->
        mkAST (ELet (name, astReducer bind red, astReducer body red))
    | ELetRec (name, bind, body) ->
        mkAST (ELetRec (name, astReducer bind red, astReducer body red))
    | EAp (e0, e1) ->
        mkAST (EAp (astReducer e0 red, astReducer e1 red))
    | EIf (e0, e1, e2) ->
        mkAST (EIf (astReducer e0 red, astReducer e1 red, astReducer e2 red))
    | EAdd (e0, e1) ->
        mkAST (EAdd (astReducer e0 red, astReducer e1 red))
    | ESub (e0, e1) ->
        mkAST (ESub (astReducer e0 red, astReducer e1 red))
    | EMul (e0, e1) ->
        mkAST (EMul (astReducer e0 red, astReducer e1 red))
    | EGt (e0, e1) ->
        mkAST (EGt (astReducer e0 red, astReducer e1 red))
    | EEq (e0, e1) ->
        mkAST (EEq (astReducer e0 red, astReducer e1 red))
    | EVar _
    | ENull
    | ENum _ ->
        ast'
    | _ ->
        failwithf "unrecognised node %A" ast'.Expr
        ast'

// eta reduction step:
// (\x -> f x) ==> f
let rec eta (node:ASTNode) : ASTNode =
    match node.Expr with
    | EFunc (arg, body) ->
        match body.Expr with
        | EAp (f, f_arg) ->
            match f_arg.Expr with
            | EVar arg1 when arg1 = arg ->
                eta f
            | _ ->
                node
        | _ ->
            let red = eta body
            if red = body then node
            else eta (mkAST (EFunc (arg, red)))
    | _ ->
        node

let etaRedex node =
    astReducer node eta

// Return a list of free (unbound) variables in expression 'node'
let rec freeVars (expr:Expr) : string list =
    match expr with
    | EVar x -> List.singleton x
    | EFunc (y, body) ->
        freeVars body.Expr |> List.except [y]
    | EAp (e1, e2) ->
        List.append (freeVars e1.Expr) (freeVars e2.Expr)

// global counter for generating unique variable names
let private nameId = ref 0

// Substitute a free variable 'x' for the term y in the 'node'
let substFreeVar (x:string) (y:Expr) (node:ASTNode) =
    let newVarName () =
        let id = !nameId
        nameId := id + 1 ;
        "z" + (string id)
    let rec substFreeVarInner x y (node:ASTNode) =
        match node.Expr with
        | EVar x' when x' = x ->
            mkAST y
        | EFunc (x', body) when x' = x ->
            node
        | EFunc (name, body) ->  // here name <> x
            let yFreeVars = freeVars y
            if List.contains name yFreeVars then
                let z = newVarName ()
                let newBody = substFreeVarInner name (EVar z) body
                mkAST (EFunc (z, substFreeVarInner x y newBody))
            else
                mkAST (EFunc (name, substFreeVarInner x y body))
        | _ ->
            node
    in astReducer node (fun node -> substFreeVarInner x y node)


let rec astInsertEval (ast:ASTNode) (ty:Map<int,LHType>) : ASTNode =
    match ast.Expr with
    | EAp (e1, e2) ->
        let t =
            match (Map.tryFind ast.Id ty) with
            | Some v -> v
            | None -> failwithf "failed to find type for %A" ast
        if (t = LHTypes.Int 256 ||
            t = LHTypes.Bool ||
            t = LHTypes.String) then
              mkAST (EEval ast)
        else
            mkAST (EAp (astInsertEval e1 ty, astInsertEval e2 ty))
    | EFunc (arg, body) ->
        mkAST (EFunc (arg, astInsertEval body ty))
    | ELet (name, bind, body) ->
        mkAST (ELet (name, astInsertEval bind ty, astInsertEval body ty))
    | ELetRec (name, bind, body) ->
        mkAST (ELetRec (name, astInsertEval bind ty, astInsertEval body ty))
    | EIf (e0, e1, e2) ->
        mkAST (EIf (astInsertEval e0 ty, astInsertEval e1 ty, astInsertEval e2 ty))
    | EAdd (e0, e1) ->
        mkAST (EAdd (astInsertEval e0 ty, astInsertEval e1 ty))
    | ESub (e0, e1) ->
        mkAST (ESub (astInsertEval e0 ty, astInsertEval e1 ty))
    | EMul (e0, e1) ->
        mkAST (EMul (astInsertEval e0 ty, astInsertEval e1 ty))
    | EGt (e0, e1) ->
        mkAST (EGt (astInsertEval e0 ty, astInsertEval e1 ty))
    | EVar _
    | ENum _
    | ENull ->
        ast
    | EEval e ->
        mkAST (EEval (astInsertEval e ty))
    | EFix e ->
        failwith "EFix shall not appear here"
    | _ ->
        failwithf "Unsupported ast node = %A" ast

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

let compileIntoFiftDebug ast debug : string =
    let ast' = etaRedex ast
    let (ty, (oldMap, newMap)) = LHTypeInfer.typeInferenceDebug (Map []) ast' debug // get types for all AST nodes
    let ast'' = astInsertEval ast' newMap // AST with EEval nodes inserted into the right places
    let ir = compile ast'' []
    if debug then
        printfn "FullAST = %O" ast ;
        printfn "AST = %O" (ast''.toSExpr()) ;
        printfn "Types = %A" (Map.toList newMap) ;
        printfn "IR = %A" ir
    List.singleton "\"Asm.fif\" include" @
    List.singleton "<{ " @
    List.singleton   fixpointImpl @
    List.singleton   (compileToTVM ir) @
    List.singleton " }>s 1000000 gasrunvmcode drop .dump cr .dump cr"
    |> String.concat "\n"

let compileIntoFift ast =
    compileIntoFiftDebug ast false
