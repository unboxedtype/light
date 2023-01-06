// Description:
//    Transforms a prototypical AST to Fift script.
// Author:
//    Evgeniy Shishkin <evgeniy.shishkin@gmail.com>
// Date:
//    Jan 2023

module AST2Fift

open System
open FSharp.Collections

let FiftHeader =
    ["\"Asm.fif\" include"; "<{"]

let FiftFooter =
    ["}>s"; "runvmcode"; ".dump"; "cr"; ".dump"]

let WhiteSpace = " ";

// ===========================================================
// TVM instructions used in the code generation
// ===========================================================
let TVM_INT = "INT";
let TVM_NIL = "NIL";
let TVM_FIRST = "FIRST";
let TVM_SECOND = "SECOND";
let TVM_NOT = "NOT";
let TVM_EQUAL = "EQUAL";
let TVM_CONS = "CONS";
let TVM_ADD = "ADD";

// ===========================================================
// Lighthouse IR expression type
// ===========================================================
type IRExpr =
    | Number of value: int
    | List of value: IRList
    | ListHead of value: IRExpr
    | ListTail of value: IRExpr
    | Add of l: IRExpr * r: IRExpr
    | BoolVal of v: BoolExpr
    | Bind of name: string * prms: string list * body: IRExpr
    | Eval of name: string * prms: IRExpr list
and BoolExpr =
    | Bool of v : bool
    | Gt of  l: BoolExpr * r: BoolExpr
    | Lt of l: BoolExpr * r: BoolExpr
    | Or of l: BoolExpr * r: BoolExpr
    | And of l: BoolExpr * r: BoolExpr
    | Not of l: BoolExpr
    | Eq of l: IRExpr * r: IRExpr
and IRList =
    | Nil
    | Cons of h: IRExpr * t: IRList

exception ASTException of string

type Context = Map<string, string list * IRExpr>
// var name -> (param list, body)
// for variables, param list = [], body is the value

// transforms AST to Fift script
let rec EvalIRExpr (p: IRExpr) (ctx: Context) =
    match p with
        | Number v ->
            [v.ToString() + WhiteSpace + TVM_INT]
        | Add (l, r) ->
            (EvalIRExpr l ctx) @ (EvalIRExpr r ctx) @ [TVM_ADD]
        | BoolVal v ->
            EvalBoolExpr v ctx
        | Eval (name, []) ->
            EvalIRExpr (snd ctx.[name]) ctx
        | List l ->
            EvalIRList l ctx
        | ListHead l ->
            (EvalIRExpr l ctx) @ [TVM_FIRST]
        | ListTail l ->
            (EvalIRExpr l ctx) @ [TVM_SECOND]
        | _ ->
            raise (ASTException "Unsupported AST element")
and EvalBoolExpr (p: BoolExpr) (ctx: Context) =
    match p with
        | Not v ->
            (EvalBoolExpr v ctx) @ [TVM_NOT]
        | Eq (l1, l2) ->
            (EvalIRExpr l1 ctx) @ (EvalIRExpr l2 ctx) @ [TVM_EQUAL]
        | Bool false ->
            ["0" + WhiteSpace + TVM_INT]
        | Bool true ->
            ["-1" + WhiteSpace + TVM_INT]
        | _ ->
            raise (ASTException "Unsupported BoolExpr element")
and EvalIRList (l: IRList) (ctx: Context) =
    match l with
        | Nil ->
            [TVM_NIL]
        | Cons (h, t) ->
            (EvalIRExpr h ctx) @ (EvalIRList t ctx) @ [TVM_CONS]
