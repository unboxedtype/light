// Description:
//    Transforms a prototypical AST to Fift script.
// Author:
//    Evgeniy Shishkin <evgeniy.shishkin@gmail.com>
// Date:
//    Jan 2023

module AST2Fift

open System
open FSharp.Collections

let fiftHeader =
    ["\"Asm.fif\" include"; "<{"]

let fiftFooter =
    ["}>s"; "runvmcode drop .s"]

// ===========================================================
// Lighthouse IR expression type
// ===========================================================
type IRExpr =
    | Number of value: int
    | List of value: IRList
    | Var of name: string
    | Add of l: IRExpr * r: IRExpr
    | BoolVal of v: BoolExpr
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
    | Cons of v: IRExpr

exception ASTException of string

type Context = Map<string, IRExpr>

// transforms AST to Fift script
let rec EvalIRExpr (p: IRExpr) (ctx: Context) =
    match p with
        | Number v ->
            [sprintf "%d INT" v]
        | Add (l, r) ->
            (EvalIRExpr l ctx) @ (EvalIRExpr r ctx) @ ["ADD"]
        | BoolVal v ->
            (EvalBoolExpr v ctx)
        | _ ->
            raise (ASTException "Unsupported AST element")
and EvalBoolExpr (p: BoolExpr) (ctx: Context) =
    match p with
        | Not v ->
            (EvalBoolExpr v ctx) @ ["NOT"]
        | Eq (l1, l2) ->
            (EvalIRExpr l1 ctx) @ (EvalIRExpr l2 ctx) @ ["EQUAL"]
        | Bool false ->
            ["0 INT"]
        | Bool true ->
            ["-1 INT"]
        | _ ->
            raise (ASTException "Unsupported BoolExpr element")

[<EntryPoint>]
let main argv =
    let ctx = Map []
    let fift = EvalIRExpr (BoolVal (Not (Not (Bool false)))) ctx
    let program = fiftHeader @ fift @ fiftFooter
    List.map (printfn "%s") program |> ignore
    0
