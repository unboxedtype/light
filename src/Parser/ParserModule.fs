// For emacs: -*- fsharp -*-

module ParserModule

open LHTypes
open type LHMachine.Expr

type Decl =
    | TypeDef of name:string * t:LHTypes.Type
    | HandlerDef of name:string * pars:LHTypes.VariableList * body:LHMachine.Expr
    | LetBinding of name:string * recs:bool * body:LHMachine.Expr

type Module =
    | Module of name:string * defs:Decl list
