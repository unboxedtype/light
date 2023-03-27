module ParserModule

open LHTypes

type ValueConstant =
    | Int of n:int
    | String of s:string

type VarDecl = string * string

type TypeDecl =
    | ProdType of vars:VarDecl list
    | SumType of ctors: (string * VarDecl) list

type Decl =
    | TypeDef of name:string * t:TypeDecl
    // | FunctionDef (name:string) (paramos:Param list) (body:FunctionBody)
    // | HandlerDef (name:string) (params:Param list) (body:HandlerBody)
   
type Module =
    | Module of name:string * defs:Decl list
