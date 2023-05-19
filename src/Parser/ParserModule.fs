// For emacs: -*- fsharp -*-

module ParserModule

open LHTypes
open LHExpr
open FSharp.Text.Lexing

type Expr =
    LHExpr.Expr

type Decl =
    | TypeDef of name:string * t:LHTypes.Type
    | HandlerDef of name:string * pars:LHTypes.VariableList * body:ASTNode
    | LetBinding of name:string * recs:bool * body:ASTNode
    member this.unboxTypeDef =
        match this with
        | TypeDef (n, t) -> (n, t)
        | _ -> failwith "Not a TypeDef value"
    member this.letBinding =
        match this with
        | LetBinding (n,isRec,body) -> (n,isRec,body)
        | _ -> failwith "Not a LetBinding value"
    member this.handlerDef =
        match this with
        | HandlerDef (n,varList,body) -> (n,varList,body)
        | _ -> failwith "Not a HandlerDef value"

type Module =
    | Module of name:string * defs:Decl list
    member this.Decls =
        match this with
        | Module (name, decls) ->
            decls
        | _ ->
            failwith "Unsupported module object"
