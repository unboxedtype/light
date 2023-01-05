// Description:
//    Transforms a prototypical AST to Fift script.
// Author:
//    Evgeniy Shishkin <evgeniy.shishkin@gmail.com>
// Date:
//    Jan 2023

module AST2Fift

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

// transforms AST to Fift script
let AST2Fift (p: AST) = "(empty)"

[<EntryPoint>]
let main argv =
    let fift = AST2Fift (BoolVal false)
    printfn "%s" fift
    0
