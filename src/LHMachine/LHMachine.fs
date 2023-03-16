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
    | GetGlob of name: Name
    | Pushint of v: int
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
    | Casejump of (int * LHCode) list
    | DumpStk
    | Throw of n:int
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
//    | EFunc of name:Name   // variable of type Func
    | EVar of name:Name // variable of type Int
    | ENum of n:int
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
    | EVar v ->
        argCount e ft
    | EAp (e1, e2) ->
        (arity e1 ft) - 1
    | EIf (c, t, f) ->
        // The type system must guarantee that
        // the arity of both branches is the same.
        arity t ft
    | _ ->
        failwith "non executable code doesn't have an arity"

let rec compile (ast:Expr) (env: Environment) (ft: FuncArityTable) : LHCode =
    match ast with
    | EVar v ->
        let r = List.tryPick (fun (n, v') ->
                  if v' = v then Some n else None) env
        match r with
            | Some n ->
                [Push n]
            | _ ->
                [GetGlob v] @
                (if ft.[v] = 0 then [Execute] else [])
    | ENum n ->
        [Pushint n]
    | EAp (e1, e2) ->
        (compile e2 env ft) @ (compile e1 (argOffset 1 env) ft) @
        (let e1ar = arity e1 ft
         if e1ar = 1 then [Execute] else [])
    | EIf (e0, t, f) ->
        (compile e0 env ft) @ [IfElse (compile t env ft, compile f env ft)]
    | EAdd (e0, e1) ->
        (compile e0 env ft) @ (compile e1 (argOffset 1 env) ft) @ [Add]
    | ESub (e0, e1) ->
        (compile e0 env ft) @ (compile e1 (argOffset 1 env) ft) @ [Sub]
    | EMul (e0, e1) ->
        (compile e0 env ft) @ (compile e1 (argOffset 1 env) ft) @ [Mul]
    | EEq (e0, e1) ->
        (compile e0 env ft) @ (compile e1 (argOffset 1 env) ft) @ [Equal]
    | EGt (e0, e1) ->
        (compile e0 env ft) @ (compile e1 (argOffset 1 env) ft) @ [Greater]
    | EPack (tag, arity, args) ->
        List.concat
          (List.map (fun (i, e) -> compile e (argOffset i env) ft)
          (List.indexed args)) @
        [Pack (tag, arity)]
    | _ ->
        failwith "not implemented"

type LHGlobalsDefs = (Name * (string list) * Expr) list
type LHGlobalsTable = (int * (string * LHCode)) list

let globalsBaseNumber = 1

let compileGlobals (globals: LHGlobalsDefs) (ft:FuncArityTable) : LHGlobalsTable =
    // ft could have been generated from globals, but...
    globals
    |> List.map
       (fun (name,vars,expr) ->
        let indVars = List.indexed vars
        (name, (compile expr indVars ft) @ [Slide ft.[name]]))
    |> List.indexed
    |> List.map (fun (n,t) -> (n + globalsBaseNumber, t))

let rec instrToTVM (i:Instruction) : string =
    match i with
    | GetGlob n -> n + " GETGLOB"
    | Pushint n -> (string n) + " INT"
    | Push n -> "s" + (string n) + " PUSH"
    | Pop n -> "s" + (string n) + " POP"
    | Slide n -> String.concat " " [for i in [1..n] -> "NIP"]
    | Execute -> "EXECUTE"
    | Add -> "ADD"
    | Sub -> "SUB"
    | Mul -> "MUL"
    | Equal -> "EQUAL"
    | Greater -> "GREATER"
    | IfElse (t, f) ->
        (generateFiftFunction t) + " " +
        (generateFiftFunction f) + " IFELSE"
    | DumpStk -> "DUMPSTK"
    | Throw n -> (string n) + " THROW"
    | Pack (tag, arity) ->
        (string arity) + " TUPLE" +
        " " + (string tag) + " INT" +
        " SWAP" +
        " 2 TUPLE"
    | _ ->
        failwith (sprintf "unimplemented instruction %A"  i)
and generateFiftFunction (code:LHCode) : string =
    let contBody =
        code
        |> List.map instrToTVM
        |> String.concat " "
    "<{ " + contBody + " }> PUSHCONT"

let generateFiftGlobFunction (name:string, code:LHCode) : string =
    (generateFiftFunction code) + " " + name + " SETGLOB"

let defineFiftNames (t:LHGlobalsTable) : string list =
    t
    |> List.map (fun (i, (name, _)) ->
                 "{ " + (string i) + " } : " + name)

let generateFift (t:LHGlobalsTable) : string =
    (List.singleton "\"Asm.fif\" include" @
     (defineFiftNames t) @
     List.singleton "<{ " @
     (t
      |> List.map snd
      |> List.map generateFiftGlobFunction) @
     List.singleton "main GETGLOB EXECUTE" @
     List.singleton " }>s 1000000 gasrunvmcode drop .dump cr .dump cr")
    |> String.concat "\n"
