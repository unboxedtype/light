// Description:
//    Transforms a prototypical AST to Fift script.
// Author:
//    Evgeniy Shishkin <evgeniy.shishkin@gmail.com>
// Date:
//    Jan 2023

module AST2Fift

open System

let fiftHeader =
    ["\"Asm.fif\" include"; "<{"]

let fiftFooter =
    ["}>s"; "runvmcode drop .s"]

// Lighthouse IR expression type

type IRExpr =
    | NumVal of value : int
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

exception ASTException of string

// transforms AST to Fift script
let rec EvalIRExpr (p: IRExpr) =
    match p with
        | NumVal v ->
            [sprintf "%d INT" v]
        | Add (l, r) ->
            (EvalIRExpr l) @ (EvalIRExpr r) @ ["ADD"]
        | BoolVal v ->
            (EvalBoolExpr v)
        | _ ->
            raise (ASTException "Unsupported AST element")
and EvalBoolExpr (p: BoolExpr) =
    match p with
        | Not v ->
            (EvalBoolExpr v) @ ["NOT"]
        | Eq (l1, l2) ->
            (EvalIRExpr l1) @ (EvalIRExpr l2) @ ["EQUAL"]
        | Bool false ->
            ["0 INT"]
        | Bool true ->
            ["-1 INT"]
        | _ ->
            raise (ASTException "Unsupported BoolExpr element")

[<EntryPoint>]
let main argv =
    let fift = EvalIRExpr (BoolVal (Not (Not (Bool false))))
    let program = fiftHeader @ fift @ fiftFooter
    List.map (printfn "%s") program |> ignore
    0
