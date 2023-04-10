// For emacs: -*- fsharp -*-

module ParserModule

open LHTypes
open type LHMachine.Expr

type ValueConstant =
    | Int of n:int
    | String of s:string

type VarDecl = string * string

// Constructor declaration consists of:
// - A name of the constructor
// - A list of (name,type) pairs of the constructor arguments
type CtorDecl = string * (VarDecl list)

type TypeDecl =
    | ProdType of vars: VarDecl list
    | SumType of ctors: CtorDecl list

type Decl =
    | TypeDef of name:string * t:TypeDecl
    | HandlerDef of name:string * pars:VarDecl list * body:LHMachine.Expr
    | LetBinding of name:string * recs:bool * body:LHMachine.Expr

type Module =
    | Module of name:string * defs:Decl list
