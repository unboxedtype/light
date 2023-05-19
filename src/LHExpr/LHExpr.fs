// For emacs: -*- fsharp -*-

// Lighthouse language AST node type.
// Here, the AST is untyped. We supply type for each
// node somewhere else.

module LHExpr

// global counter for generating new AST IDs
let private currentId = ref 0

type Name = string

// AST Expression
type Expr =
    | ENum of n:int                     // value of type Int
    | ENull                             // value Null (unit)
    | EFunc of arg:Name * body:ASTNode     // value of type Function<T1,T2>
    | EVar of name:Name                 // value of the variable
    | EEval of e:ASTNode                   // evaluate saturated function
    | EAp of e1:ASTNode * e2:ASTNode
    | ELet of name:Name * bind:ASTNode * body:ASTNode
    | ELetRec of name:Name * bind:ASTNode * body:ASTNode
    | EFix of e0:ASTNode   // needed to properly derive type of fixpoint (letrec)
                        // not used during the evaluation
    | EIf of e0:ASTNode * e1:ASTNode * e2:ASTNode
    | EAdd of e0:ASTNode * e1:ASTNode
    | ESub of e0:ASTNode * e1:ASTNode
    | EMul of e0:ASTNode * e1:ASTNode
    | EEq of e0:ASTNode * e1:ASTNode
    | EGt of e0:ASTNode * e1:ASTNode
    | ECase of c:ASTNode * cs:(int * (Name list) * ASTNode) list
    | EPack of tag:int * arity:int * args:ASTNode list
    | ESelect of e0:ASTNode * e1:ASTNode
    | ERecord of es:ASTNode list
    | EUpdateRec of e0:ASTNode * n:int * e1:ASTNode
    | EAssign of e0:ASTNode
    | EAsm of s:string
    member this.Name =
        match this with
        | ENum n -> sprintf "%A" this
        | ENull -> "ENull"
        | EFunc (arg, body) -> sprintf "EFunc (%A, ...) " arg
        | EVar n -> sprintf "%A" this
        | EAp (e1, e2) -> "EAp"
        | ELet (name, _, _) -> sprintf "ELet (%A, ...)" name
        | ELetRec (name, _, _) -> sprintf "ELetRec (%A, ...)" name
        | EIf (_, _, _) -> "EIf"
        | EAdd (_, _) -> "EAdd"
        | ESub (_, _) -> "ESub"
        | EMul (_, _) -> "EMul"
        | EGt (_, _) -> "EGt"
        | EEq (_, _) -> "EEq"
        | EFix _ -> "EFix"
        | _ -> failwithf "undefined term: %A" this
// and CaseAlt<'T> = int * (Name list) * 'T   // case (tag:0) (vars: ["x","y"]) -> x + y
and ASTNode =
    | ASTNode of id:int * expr:Expr
    member this.Id =
        match this with
        | ASTNode (id, _) -> id
        | _ -> failwithf "unsupported AST node type"
    member this.Expr =
        match this with
        | ASTNode (_, expr) -> expr
        | _ -> failwithf "unsupported AST node type"
    static member newId () =
        let id = !currentId
        currentId := id + 1
        id
