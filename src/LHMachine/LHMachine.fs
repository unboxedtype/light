// For emacs: -*- fsharp -*-
module LHMachine

open System
open System.Collections.Generic

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
    | Split of n:int
    | Select of n:int // take the n-th field of the record
    | UpdateRec of n:int // update the n-th field of the record
    | Casejump of (int * LHCode) list
    | DumpStk
    | Throw of n:int
    | Alloc of n:int  // allocate n Null values on the stack
    | Update of i:int // update the i-th stack value with the one residing on the top
and LHCode = Instruction list

// type LHDump = LHCode * LHStack
// type LHState = LHCode * LHStack * LHGlobals * LHDump

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
    | ESelect of e:Expr * n:int
    | EUpdateRec of e0:Expr * n:int * e1:Expr
    | EUpdateState of e0:Expr
and CaseAlt = int * (Name list) * Expr   // case (tag:0) (vars: ["x","y"]) -> x + y
and BoundVarDefs = (Name * Expr) list

// combinator name, number of arguments (arity), code
type LHCompiledSC = Name * int * LHCode

// shift all indexes on m places
let argOffset (m:int) (env: Environment) =
    [for (n, v) in env -> (n + m, v)]

// A mapping between a combinator name and its arity
// let fact n =  ..
// let sum a b = ...
// let main = ...
// FuncArityTable = [("fact",1); ("sum",2); ("main",0)]
type FuncArityTable = Map<Name,int>

let rec argCount (e:Expr) (ft:FuncArityTable) : int =
    match e with
    | EVar v ->
        ft.[v]
    | EAp (e1, e2) ->
        argCount e1 ft
    | _ ->
        failwith "argCount applies only to function identifiers and applications"

let rec arity (e:Expr) (ft:FuncArityTable) : int =
    match e with
    | ESelect (_, _) ->
        1 // this idea here is that all stored functions
          // have the arity 1 due to currying;
          // f : int -> int -> int is actually int -> (int -> int)
    | EFunc (_, _) ->
        1
    | EVar v ->
        argCount e ft
    | EAp (e1, e2) ->
        (arity e1 ft) - 1
    | EIf (c, t, f) ->
        // The type system must guarantee that
        // the arity of both branches is the same
        arity t ft
    | _ ->
        failwith "non executable code doesn't have an arity"

let compileArgs (defs:BoundVarDefs) (env:Environment) : Environment =
    let n = List.length defs
    let indexes = List.rev [for i in 0 .. (n-1) -> i]
    let names = List.map fst defs
    (List.zip indexes names) @ (argOffset n env)

let rec compile (ast:Expr) (env: Environment) (ft: FuncArityTable) (depth:int) : LHCode =
    match ast with
    | EVar v ->
        let r = List.tryPick (fun (n, v') ->
                  if v' = v then Some n else None) env
        match r with
            | Some n ->
                [Push n]
            | _ ->
                [GetGlob v]
    | ENum n ->
        [Integer n]
    | EFunc (argName, body) ->
        let env' = (0, argName) :: (argOffset 1 env)
        match body with
        | EFunc (_, _) ->
            compile body env' ft 0
        | _ ->
            [Function (compile body env' ft 0)]
    | ENull ->
        [Null]
    | EEval e ->
        (compile e env ft 0) @ [Execute]
    | EAp (e1, e2) ->
        (compile e2 env ft 0) @
        (compile e1 (argOffset 1 env) ft 0) @
        [Apply]
    | EIf (e0, t, f) ->
        (compile e0 env ft 0) @ [IfElse (compile t env ft 0, compile f env ft 0)]
    | EAdd (e0, e1) ->
        (compile e0 env ft 0) @ (compile e1 (argOffset 1 env) ft 0) @ [Add]
    | ESub (e0, e1) ->
        (compile e0 env ft 0) @ (compile e1 (argOffset 1 env) ft 0) @ [Sub]
    | EMul (e0, e1) ->
        (compile e0 env ft 0) @ (compile e1 (argOffset 1 env) ft 0) @ [Mul]
    | EEq (e0, e1) ->
        (compile e0 env ft 0) @ (compile e1 (argOffset 1 env) ft 0) @ [Equal]
    | EGt (e0, e1) ->
        (compile e0 env ft 0) @ (compile e1 (argOffset 1 env) ft 0) @ [Greater]
    | EPack (tag, arity, args) ->
        List.concat
          (List.map (fun (i, e) -> compile e (argOffset i env) ft 0)
          (List.indexed args)) @
        [Pack (tag, arity)]
    | ECase (e, alts) ->
        (compile e env ft 0) @ [ Casejump (compileAlts alts env ft) ]
    | ELet (isRec, defs, body) ->
        match isRec with
        | false ->
            compileLet defs body env ft
        | true ->
            compileLetRec defs body env ft
    | ESelect (e, n) ->
        (compile e env ft 0) @ [Select n]
    | EUpdateRec (e, n, e1) ->
        (compile e env ft 0) @ (compile e1 (argOffset 1 env) ft 0) @ [UpdateRec n]
    | EUpdateState e ->
        (compile e env ft 0) @ [SetGlob "1"] @ [Null]
    | _ ->
        failwith "not implemented"
and compileAlts alts env ft =
    List.map (fun a ->
                 let (tag, names, body) = a
                 let indexed = List.indexed (List.rev names)
                 let env_len = List.length names
                 let env' = indexed @ (argOffset env_len env)
                 (tag, compileAlt env_len body env' ft)
              ) alts
and compileAlt offset expr env ft =
    [Split offset] @ (compile expr env ft 0) @ [Slide offset]
and compileLet (defs: BoundVarDefs) expr env ft =
    // inject new definitions into the environment
    let env' = compileArgs defs env
    let n = List.length defs
    // compile the definitions using the old environment
    (compileLetDefs defs env ft) @
      // compile the expression using the new environment
      (compile expr env' ft 0) @
      // remove local variables after the evaluation
      [Slide n]
and compileLetDefs defs env ft =
    match defs with
        | [] ->
            []
        | (name, expr) :: defs' ->
            (compile expr env ft 0) @ compileLetDefs defs' (argOffset 1 env) ft
and compileLetRec (defs: BoundVarDefs) expr env ft =
    let env' = compileArgs defs env
    let n = List.length defs
    [Alloc n] @ (compileLetRecDefs defs env' n ft) @ (compile expr env' ft 0) @ [Slide n]
and compileLetRecDefs defs env n ft =
    match defs with
        | [] ->
            []
        | (name, expr) :: defs' ->
            (compile expr env ft 0) @ [Update n] @ compileLetRecDefs defs' env (n - 1) ft

type LHGlobalsDefs = (Name * (string list) * Expr) list
type LHGlobalsTable = (int * (string * LHCode)) list

let globalsBaseNumber = 2

let compileGlobals (globals: LHGlobalsDefs) (ft:FuncArityTable) : LHGlobalsTable =
    // ft could have been generated from globals, but...
    globals
    |> List.map
       (fun (name,vars,expr) ->
        let indVars = List.indexed vars
        (name, (compile expr indVars ft 0) @ [Slide ft.[name]]))
    |> List.indexed
    |> List.map (fun (n,t) -> (n + globalsBaseNumber, t))

let rec instrToTVM (i:Instruction) : string =
    match i with
    | Null -> "NULL"
    | Alloc n -> String.concat " " [for i in [1..n] -> "NULL"]
    | Apply ->  "<{ DEPTH DEC ZERO DEC SETCONTVARARGS }> PUSHCONT 2 1 CALLXARGS" // inject one argument and receive a new function in return
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
                "<{ DROP " + compileToTVM code + " EXECUTE }> PUSHCONT IFJMP " +
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

let generateFift (t:LHGlobalsTable) (stateReader:string) (stateWriter:string) (dataCell:string) : string =
    let dataCell' =
        if dataCell <> "" then dataCell
        else "<b b>"
    (List.singleton "\"Asm.fif\" include" @
     (defineFiftNames t) @
     List.singleton "<{ " @
     (t
      |> List.map snd
      |> List.map mkFiftGlobFunction) @
     (if stateReader <> "" then
         List.singleton stateReader @
         List.singleton "1 SETGLOB" @
         List.singleton "<{ 1 GETGLOB }> PUSHCONT" @
         List.singleton "state SETGLOB"
      else []) @
     List.singleton "NULL main GETGLOB 1 1 CALLXARGS" @
     List.singleton stateWriter @
     List.singleton (" }>s " + dataCell' + " 1000000 gasrunvm drop drop .dump cr .dump cr"))
    |> String.concat "\n"
