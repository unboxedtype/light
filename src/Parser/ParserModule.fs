// For emacs: -*- fsharp -*-

module ParserModule

open LHTypes
open LHExpr
open FSharp.Text.Lexing

type Type = LHTypes.Type

type Expr =
    LHExpr.Expr

type Decl =
    | TypeDef of name:string * t:Type
    | HandlerDef of name:string * pars:list<string*option<Type>> * body:ASTNode
    | LetBinding of name:string * pars:list<string*option<Type>> * recs:bool * body:ASTNode
    member this.typeDef =
        match this with
        | TypeDef (n, t) -> (n, t)
        | _ -> failwith "Not a TypeDef value"
    member this.letBinding =
        match this with
        | LetBinding (n,varList,isRec,body) -> (n,varList,isRec,body)
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
