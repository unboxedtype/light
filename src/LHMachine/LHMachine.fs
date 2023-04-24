// For emacs: -*- fsharp -*-

// Here we compile AST into LHMachine abstract VM code.
// Later, that code gets compiled into the TVM code.

// TODO: separate module into two : LHMachine and LHCompiler.

module LHMachine

open System
open System.Collections.Generic
open type LHTypes.Type

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
    | Select of n:int    // take the n-th field of the record
    | UpdateRec of n:int // update the n-th field of the record
    | Casejump of (int * LHCode) list
    | DumpStk
    | Throw of n:int
    | Alloc of n:int  // allocate n Null values on the stack
    | Update of i:int // update the i-th stack value with the one residing on the top
and LHCode = Instruction list

// index + variable name
// [(1,"x"); (2,"y"); ...]
// index is needed to know the offset of the variables pointer
// in the stack in case of nested calls
type Environment = (int * Name) list

// AST Expression node
type Expr =
    | EFunc of arg:Name * body:Expr     // value of type Function<T1,T2>
    | EVar of name:Name                 // value of the variable
    | ENum of n:int                     // value of type Int
    | ENull                             // value Null (unit)
    | EEval of e:Expr                   // evaluate saturated function
    | EAp of e1:Expr * e2:Expr
    | ELet of isRec:bool * defs:BoundVarDefs * body:Expr
    | EIf of e0:Expr * e1:Expr * e2:Expr
    | EAdd of e0:Expr * e1:Expr
    | ESub of e0:Expr * e1:Expr
    | EMul of e0:Expr * e1:Expr
    | EEq of e0:Expr * e1:Expr
    | EGt of e0:Expr * e1:Expr
    | ECase of c:Expr * cs:CaseAlt list
    | EPack of tag:int * arity:int * args:Expr list
    | ESelect of e0:Expr * e1:Expr
    | ERecord of es:Expr list
    | EUpdateRec of e0:Expr * n:int * e1:Expr
    | EAssign of e0:Expr
and CaseAlt = int * (Name list) * Expr   // case (tag:0) (vars: ["x","y"]) -> x + y
and BoundVarDefs = (Name * Expr) list

// combinator name, number of arguments (arity), code
type LHCompiledSC = Name * int * LHCode

// shift all indexes on m places
let argOffset (m:int) (env: Environment) =
    [for (n, v) in env -> (n + m, v)]

let compileArgs (defs:BoundVarDefs) (env:Environment) : Environment =
    let n = List.length defs
    let indexes = List.rev [for i in 0 .. (n-1) -> i]
    let names = List.map fst defs
    (List.zip indexes names) @ (argOffset n env)

let rec compileWithTypes (ast:Expr) (env:Environment) (ty:LHTypes.ProgramTypes) : LHCode =
    match ast with
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
            | h :: t -> (compileWithTypes h env' ty) @ compileExprs t (argOffset 1 env')
        let n = List.length es
        (compileExprs es env) @ [Record n]
    | EFunc (argName, body) ->
        let env' = (0, argName) :: (argOffset 1 env)
        match body with
        | EFunc (_, _) ->
            compileWithTypes body env' ty
        | _ ->
            [Function (compileWithTypes body env' ty)]
    | ENull ->
        [Null]
    | EEval e ->
        (compileWithTypes e env ty) @ [Execute]
    | EAp (e1, e2) ->
        (compileWithTypes e2 env ty) @
        (compileWithTypes e1 (argOffset 1 env) ty) @
        [Apply]
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
    | ELet (isRec, defs, body) ->
        match isRec with
        | false ->
            compileLet defs body env ty
        | true ->
            compileLetRec defs body env ty
    | ESelect (e0, e1) ->
        match (e0, e1) with
        | (EVar s, EVar x) ->
            // n = lookup x position in the record definition of e0
            // Currently,the lookup operator '.' is only allowed to be
            // used with records. To compile this expression, we need
            // to find out the index of the "x" field. For that, we need
            // to access type information of e0.
            let stype = LHTypes.findType s ty     // findType "state" [("state",UserType "State"); ...]
            let ptype = LHTypes.findType stype.usertypeName ty // findType
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
        (compileWithTypes e env ty) @ (compileWithTypes e1 (argOffset 1 env) ty) @ [UpdateRec n]
    | EAssign e ->
        (compileWithTypes e env ty) @ [SetGlob "2"] @ [Null]
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
and compileLetRec (defs: BoundVarDefs) expr env ty =
    let env' = compileArgs defs env
    let n = List.length defs
    [Alloc n] @ (compileLetRecDefs defs env' n ty) @ (compileWithTypes expr env' ty) @ [Slide n]
and compileLetRecDefs defs env n ty =
    match defs with
        | [] ->
            []
        | (name, expr) :: defs' ->
            (compileWithTypes expr env ty) @ [Update n] @ compileLetRecDefs defs' env (n - 1) ty

let compile (ast:Expr) (env: Environment) : LHCode =
    compileWithTypes ast env []


type LHGlobalsDefs = (Name * (string list) * Expr) list
type LHGlobalsTable = (int * (string * LHCode)) list

let globalsBaseNumber = 2

let compileGlobalsWithTypes (globals: LHGlobalsDefs) (ty:LHTypes.ProgramTypes) : LHGlobalsTable =
    globals
    |> List.map
       (fun (name,vars,expr) ->
        let indVars = List.indexed vars
        (name, (compileWithTypes expr indVars ty) @ [Slide 0]))
    |> List.indexed
    |> List.map (fun (n,t) -> (n + globalsBaseNumber, t))

let compileGlobals globals =
    compileGlobalsWithTypes globals []

let rec instrToTVM (i:Instruction) : string =
    match i with
    | Null -> "NULL"
    | Alloc n -> String.concat " " [for i in [1..n] -> "NULL"]
    | Apply ->  "1 GETGLOB 2 1 CALLXARGS" // inject one argument and receive a new function in return
    | Update i -> "s0 s" + (string i) + " XCHG DROP"
    | GetGlob n -> n + " GETGLOB"
    | SetGlob n -> n + " SETGLOB"
    | Integer n -> (string n) + " INT"
    | Push n -> "s" + (string n) + " PUSH"
    | Pop n -> "s" + (string n) + " POP"
    | Slide n -> String.concat " " [for i in [1..n] -> "NIP"]
    | Function b -> "<{ " + (compileToTVM b) + " }> PUSHCONT"
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
    | _ ->
        failwith (sprintf "unimplemented instruction %A"  i)
and compileToTVM (code:LHCode) : string =
    code
    |> List.map instrToTVM
    |> String.concat " "
and mkFiftCell (body: string) : string =
    "<{ " + body + "}>c "

let mkFiftGlobFunction (name:string, code:LHCode) : string =
    (compileToTVM code) + name + " SETGLOB"

let defineFiftNames (t:LHGlobalsTable) : string list =
    t
    |> List.map (fun (i, (name, _)) ->
                 "{ " + (string i) + " } : " + name)

let generateFiftExt globTable stateReader stateWriter dataCell accBalance msgBalance inMsgCell inMsgBodySlice isExtMsg : string =
    let dataCell' =
        if dataCell <> "" then dataCell
        else "<b b>"
    (List.singleton "\"Asm.fif\" include" @
     (defineFiftNames globTable) @
     List.singleton accBalance @
     List.singleton msgBalance @
     List.singleton inMsgCell @
     List.singleton inMsgBodySlice @
     List.singleton isExtMsg @
     List.singleton "<{ " @
     (globTable
      |> List.map snd
      |> List.map mkFiftGlobFunction) @
     (if stateReader <> "" then
         List.singleton stateReader @
         List.singleton "state SETGLOB"
      else []) @
     List.singleton "<{ DEPTH DEC ZERO DEC SETCONTVARARGS }> PUSHCONT 1 SETGLOB" @
     List.singleton "main GETGLOB 5 1 CALLXARGS" @
     List.singleton stateWriter @
     List.singleton (" }>s " + dataCell' + " 1000000 gasrunvm drop drop .dump cr .dump cr"))
    |> String.concat "\n"

let generateFift (t:LHGlobalsTable) (stateReader:string) (stateWriter:string) (dataCell:string) : string =
    let accBalance = "0"
    let msgBalance = "0"
    let msgCell = "<b b>"
    let msgBodySlice = "<b b> <s"
    let isExtMsg = "0"
    generateFiftExt t stateReader stateWriter dataCell accBalance msgBalance msgCell msgBodySlice isExtMsg
