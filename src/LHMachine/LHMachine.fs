// For emacs: -*- fsharp -*-

// Here we compile AST into LHMachine abstract VM code.
// Later, that code gets compiled into the TVM code.

// TODO: separate module into two : LHMachine and LHCompiler.

module LHMachine

open System
open System.Collections.Generic
open type LHTypes.Type
type LHType = LHTypes.Type
open LHExpr

exception GMError of string

// Incomplete pattern matches on this expression.
#nowarn "25"

// This rule will never be matched
#nowarn "26"

type Name = string
type Instruction =
    | Null
    | True
    | False
    | Not
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
    | Less
    | GreaterEq
    | LessEq
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
type Environment = list<int * Name>
type NodeTypeMap = Map<int,LHType>
type Expr = LHExpr.Expr
type ASTNode = LHExpr.ASTNode
type BoundVarDefs = list<Name * ASTNode>

// shift all indexes on m places
let argOffset (m:int) (env: Environment) =
    [for (n, v) in env -> (n + m, v)]

let compileArgs (defs:BoundVarDefs) (env:Environment) : Environment =
    let n = List.length defs
    let indexes = List.rev [for i in 0 .. (n-1) -> i]
    let names = List.map fst defs
    (List.zip indexes names) @ (argOffset n env)

// ty is collection of types defined in the actor code
let rec compileWithTypes (ast:ASTNode) (env:Environment) (ty:NodeTypeMap) evalNodes : LHCode =
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
    | EBool true ->
        [True]
    | EBool false ->
        [False]
    | ERecord es ->
        let rec compileExprs l env' =
            match l with
            | [] -> []
            | h :: t ->
                (compileWithTypes h env' ty evalNodes) @
                compileExprs t (argOffset 1 env')
        let es' = List.map snd es
        let n = List.length es' // now we need only values; field names are omitted.
        (compileExprs es' env) @ [Record n]
    | EFunc (argNameType, body) ->
        let env' = (0, fst argNameType) :: (argOffset 1 env)
        // If  it is a function of a single argument, then
        // pack it directly into a lamda abstraction; otherwise,
        // recursively descend one level down with one env index shifted.
        match body.Expr with
        | EFunc (_, _) ->
            compileWithTypes body env' ty evalNodes
        | _ ->
            [Function (compileWithTypes body env' ty evalNodes)]
    | ENull ->
        [Null]
    | EAp (e1, e2) ->
        (compileWithTypes e2 env ty evalNodes) @
        (compileWithTypes e1 (argOffset 1 env) ty evalNodes) @
        [Apply] @
        (if (evalNodes |> List.contains ast.Id) then [Execute]
         else [])
    | EFix f ->
        (compileWithTypes f env ty evalNodes) @
        [Fixpoint]
    // We leave EEval node only for test purposes.
    // Real compiler will not insert those into AST anymore.
    // It uses external list of node IDs that has to be "executed".
    | EEval f ->
        (compileWithTypes f env ty evalNodes) @
        [Execute]
    | EIf (e0, t, f) ->
        (compileWithTypes e0 env ty evalNodes) @
        [IfElse (compileWithTypes t env ty evalNodes,
                 compileWithTypes f env ty evalNodes)]
    | EAdd (e0, e1)
    | ESub (e0, e1)
    | EMul (e0, e1)
    | EEq (e0, e1)
    | EGt (e0, e1)
    | ELt (e0, e1)
    | EGtEq (e0, e1)
    | ELtEq (e0, e1) ->
        (compileWithTypes e0 env ty evalNodes) @
        (compileWithTypes e1 (argOffset 1 env) ty evalNodes) @
        match ast.Expr with
        | EAdd _ -> [Add]
        | ESub _ -> [Sub]
        | EMul _ -> [Mul]
        | EEq _ -> [Equal]
        | EGt _ -> [Greater]
        | ELt _ -> [Less]
        | EGtEq _ -> [GreaterEq]
        | ELtEq _ -> [LessEq]
    | EPack (tag, arity, args) ->
        List.concat
          (List.map (fun (i, e) ->
                     compileWithTypes e (argOffset i env) ty evalNodes)
          (List.indexed args)) @
        [Pack (tag, arity)]
    | ECase (e, alts) ->
        (compileWithTypes e env ty evalNodes) @ [ Casejump (compileAlts alts env ty evalNodes) ]
    | ELet (name, def, body) ->
        compileLet [(name,def)] body env ty evalNodes
    | ELetRec (name, def, body) ->
        // compileLetRec [(name,def)] body env ty
        // let rec fact = \n -> n * fact (n-1)
        //  ---> let fact = fixpoint (\fact . \n . n * fact (n - 1))
        // fact 5 --> fixpoint (fact 5)
        let expr = mkAST (ELet (name, mkAST (EFix (mkAST (EFunc ((name, None), def)))), body))
        compileWithTypes expr env ty evalNodes
    | ESelect (e0, e1) ->
        let isEval = evalNodes |> List.contains ast.Id
        match e1.Expr with
        | EVar x ->
            // n = lookup x position in the record definition of e0
            // Currently,the lookup operator '.' is only allowed to be
            // used with records. To compile this expression, we need
            // to find out the index of the "x" field. For that, we need
            // to access type information of e0.
            let stype =
               match (Map.tryFind e0.Id ty) with
               | Some v -> v
               | None ->
                   failwithf "Can't find type for the node %A, expr:%A" e0.Id ((e0.toSExpr()).ToString())
            let ptype =
                match stype with
                | UserType (n, Some ty') -> ty'
                | _ -> stype
            match ptype with
            | PT pts ->
                let n =
                    pts
                    |> List.indexed
                    |> List.find (fun (i,e) -> fst e = x)
                    |> fst
                (compileWithTypes e0 env ty evalNodes) @
                (if isEval then [Execute] else []) @
                [Select n]
            | _ ->
                failwith "the .dot operator is allowed to be used only on record types"
        | _ ->
            failwith "For the expression 'var.id', the 'id' is an explicit
                      record field name you want to access"
    | EUpdateRec (e, n, e1) ->
        (compileWithTypes e env ty evalNodes) @
        (compileWithTypes e1 (argOffset 1 env) ty evalNodes) @
        [UpdateRec n]
    | EAsm s ->
        [Asm s]
    | ETypeCast (e, _) ->
        compileWithTypes e env ty evalNodes
    | ENot e ->
        (compileWithTypes e env ty evalNodes) @ [Not]
    | EFailWith n ->
        [FailWith n]
    | _ ->
        failwithf "not implemented : %A" (ast.toSExpr())
and compileAlts alts env ty evalNodes =
    List.map (fun a ->
                 let (tag, names, body) = a
                 let indexed = List.indexed (List.rev names)
                 let env_len = List.length names
                 let env' = indexed @ (argOffset env_len env)
                 (tag, compileAlt env_len body env' ty evalNodes)
              ) alts
and compileAlt offset expr env ty evalNodes =
    [Split offset] @ (compileWithTypes expr env ty evalNodes) @ [Slide offset]
and compileLet (defs: BoundVarDefs) expr env ty evalNodes =
    // inject new definitions into the environment
    let env' = compileArgs defs env
    let n = List.length defs
    // compile the definitions using the old environment
    (compileLetDefs defs env ty evalNodes) @
      // compile the expression using the new environment
      (compileWithTypes expr env' ty evalNodes) @
      // remove local variables after the evaluation
      [Slide n]
and compileLetDefs defs env ty evalNodes =
    match defs with
        | [] ->
            []
        | (name, expr) :: defs' ->
            (compileWithTypes expr env ty evalNodes) @ compileLetDefs defs' (argOffset 1 env) ty evalNodes
// originally, this function was written to do several let-rec compilation at once,
// but later we switched to more managable "let n = expr in" single variable construct,
// nevertheless we didn't change the code, it still support multiple bindings
and compileLetRec defs expr env ty evalNodes =
    let env' = compileArgs defs env
    let n = List.length defs
    [Alloc n] @ (compileLetRecDefs defs env' n ty evalNodes) @ (compileWithTypes expr env' ty evalNodes) @ [Slide n]
and compileLetRecDefs defs env n ty evalNodes =
    match defs with
        | [] ->
            []
        | (name, node) :: defs' ->
            (compileWithTypes node env ty evalNodes) @ [Update n] @ compileLetRecDefs defs' env (n - 1) ty evalNodes

let compile (ast:ASTNode) (env: Environment) : LHCode =
    compileWithTypes ast env (Map []) []

let rec instrToTVM (i:Instruction) : string =
    match i with
    | Null -> "NULL"
    | False -> "FALSE"
    | True -> "TRUE"
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
    | Not -> "INC NEGATE"   // 0 --> -1, -1 --> 0
    | Add -> "ADD"
    | Sub -> "SUB"
    | Mul -> "MUL"
    | Equal -> "EQUAL"
    | Greater -> "GREATER"
    | Less -> "LESS"
    | GreaterEq -> "GEQ"
    | LessEq -> "LEQ"
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

let rec hasInstruction (i:Instruction) (ir:LHCode) : bool =
    match ir with
    | [] -> false
    | Fixpoint :: t -> true
    | (Function c) :: t -> (hasInstruction i c) || hasInstruction i t
    | (IfElse (tr, fl)) :: t -> hasInstruction i tr || hasInstruction i fl || hasInstruction i t
    | (Casejump cases) :: t ->
        (cases
        |> List.map (fun (_, c) -> hasInstruction i c)
        |> List.contains true) || hasInstruction i t
    | _ :: t -> hasInstruction i t

// Translation of AST into IR language, and then into FIFT commands.
// IR language is easier to debug in complex cases.
let compileIntoFiftDebug ast nodeTypeMapping evalNodes debug : string =
    let ir = compileWithTypes ast [] nodeTypeMapping evalNodes
    let hasFixpoint = ir |> hasInstruction Fixpoint
    if debug then
        printfn "IR:\n%A" ir
        printfn "hasFixpoint = %A" hasFixpoint
    List.singleton "\"Asm.fif\" include" @
    List.singleton "<{ " @
    (if hasFixpoint then [fixpointImpl] else []) @
    List.singleton   (compileToTVM ir) @
    List.singleton " }>s 1000000 gasrunvmcode drop .dump cr .dump cr"
    |> String.concat "\n"

let compileIntoFift ast =
    compileIntoFiftDebug ast (Map []) [] false

let compileWithInitialTypesDebug ast nodeTypeMapping evalNodes debug =
    compileIntoFiftDebug ast nodeTypeMapping evalNodes debug

let compileWithInitialTypes ast =
    compileWithInitialTypesDebug ast (Map []) [] false
