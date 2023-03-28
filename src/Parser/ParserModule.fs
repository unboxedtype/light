module ParserModule

open LHTypes

type ValueConstant =
    | Int of n:int
    | String of s:string

type VarDecl = string * string

// Constructor declaration consists of:
// - A name of the constructor
// - A list of (name,type) pairs of the constructor arguments
type CtorDecl = string * (VarDecl list)

type TypeDecl =
    | ProdType of vars:VarDecl list
    | SumType of ctors: CtorDecl list

type Decl =
    | TypeDef of name:string * t:TypeDecl
    // | FunctionDef (name:string) (paramos:Param list) (body:FunctionBody)
    // | HandlerDef (name:string) (params:Param list) (body:HandlerBody)
   
type Module =
    | Module of name:string * defs:Decl list
