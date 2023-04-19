// For emacs: -*- fsharp -*-

module ParserModule

open LHTypes
open type LHMachine.Expr

type Decl =
    | TypeDef of name:string * t:LHTypes.Type
    | HandlerDef of name:string * pars:LHTypes.VariableList * body:LHMachine.Expr
    | LetBinding of name:string * recs:bool * body:LHMachine.Expr
    member this.unboxTypeDef =
        match this with
        | TypeDef (n, t) -> (n, t)
        | _ -> failwith "Not a TypeDef value"
    member this.unboxLetBinding =
        match this with
        | LetBinding (n,isRec,body) -> (n,isRec,body)
        | _ -> failwith "Not a LetBinding value"
    member this.unboxHandlerDef =
        match this with
        | HandlerDef (n,varList,body) -> (n,varList,body)
        | _ -> failwith "Not a HandlerDef value"

type Module =
    | Module of name:string * defs:Decl list
