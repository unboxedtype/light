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
    | BoolVal of value : bool
    | NumVal of value : int
    | Mul of l: IRExpr * r: IRExpr
    | Add of l: IRExpr * r: IRExpr
    | Gt of  l: IRExpr * r: IRExpr
    | Lt of l: IRExpr * r: IRExpr
    | Eq of l: IRExpr * r: IRExpr
    | Or of l: IRExpr * r: IRExpr
    | And of l: IRExpr * r: IRExpr
    | Mod of l: IRExpr * r: IRExpr
    | Not of l: IRExpr

type AST = IRExpr

exception ASTException of string

// transforms AST to Fift script
let rec AST2Fift (p: AST) =
    match p with
        | BoolVal false -> ["0 INT"]
        | BoolVal true -> ["-1 INT"]
        | NumVal v -> [ sprintf "%d INT" v ]
        | Add (l, r) ->
            let l1, r1 = (AST2Fift l, AST2Fift r)
            l1 @ r1 @ ["ADD"]
        | Not v ->
            (AST2Fift v) @ ["NOT"]
        | _ ->
            raise (ASTException "Unsupported AST element")

[<EntryPoint>]
let main argv =
    let fift = AST2Fift (Not (Not (BoolVal false)))
    let program = fiftHeader @ fift @ fiftFooter
    List.map (printfn "%s") program |> ignore
    0
