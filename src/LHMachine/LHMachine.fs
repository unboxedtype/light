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
    | Casejump of (int * LHCode) list
    | Split of n:int
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
// FuncTable = [("fact",1); ("sum",2); ("main",0)]        
type FuncTable = Map<Name,int>

let rec argCount (e:Expr) (ft:FuncTable) : int =
    match e with
    | EVar v ->        
        ft.[v]
    | EAp (e1, e2) ->
        argCount e1 ft
    | _ ->
        failwith "argCount applies only to function identifiers and applications"
    
let rec arity (e:Expr) (ft:FuncTable) : int =
    match e with
        | EVar v ->
            argCount e ft
        | EAp (e1, e2) ->
            (arity e1 ft) - 1
        | EIf (c, t, f) ->
            arity t ft   // type system must guarantee that arity of both branches is the same
        | _ ->
            failwith "non executable code doesn't have an arity"

let rec compile (ast:Expr) (env: Environment) (ft: FuncTable) : LHCode =
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
        [Pushint n]
    | EAp (e1, e2) ->
        (compile e2 env ft) @ (compile e1 (argOffset 1 env) ft) @
        (if (arity e1 ft) = 1 then [Execute; Slide (argCount e1 ft)]
         else [])
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
    | _ ->
        failwith "not implemented"
        
