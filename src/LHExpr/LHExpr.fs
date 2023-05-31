// For emacs: -*- fsharp -*-

// Lighthouse language AST node type.
// Here, the AST is untyped. We supply type for each
// node somewhere else.

module LHExpr

// global counter for generating new AST IDs
let private currentId = ref 0

type Name = string

// Simplified Expression. This variant is more suitable
// for testing purposes, while ASTNode is for real compilation.
type SExpr =
    | SNum of n:int                     // value of type Int
    | SStr of s:string
    | SBool of b:bool
    | SNull                             // value Null (unit)
    | SFunc of arg:Name * body:SExpr     // value of type Function<T1,T2>
    | SVar of name:Name                 // value of the variable
    | SEval of e:SExpr                   // evaluate saturated function
    | SAp of e1:SExpr * e2:SExpr
    | SLet of name:Name * bind:SExpr * body:SExpr
    | SLetRec of name:Name * bind:SExpr * body:SExpr
    | SFix of e0:SExpr   // needed to properly derive type of fixpoint (letrec)
                        // not used during the evaluation
    | SIf of e0:SExpr * e1:SExpr * e2:SExpr
    | SAdd of e0:SExpr * e1:SExpr
    | SSub of e0:SExpr * e1:SExpr
    | SMul of e0:SExpr * e1:SExpr
    | SEq of e0:SExpr * e1:SExpr
    | SGt of e0:SExpr * e1:SExpr
    | SCase of c:SExpr * cs:(int * (Name list) * SExpr) list
    | SPack of tag:int * arity:int * args:SExpr list
    | SSelect of e0:SExpr * e1:SExpr
    | SRecord of es:(Name * SExpr) list
    | SUpdateRec of e0:SExpr * n:int * e1:SExpr
    | SAssign of e0:SExpr
    | SAsm of s:string
    | SFailWith of n:int
    override this.ToString () =
        let s = sprintf "%A" this
        let len = s.Length
        let newlen = min 200 len
        s.Substring (0, newlen) + (if (len > 200) then "..." else "")
// AST Expression
type Expr =
    | ENum of n:int                     // value of type Int
    | EStr of s:string                  // value of type String
    | EBool of b:bool
    | ENull                             // value Null (Unit)
    | EFunc of arg:Name * body:ASTNode  // value of type Function<T1,T2>
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
    | ERecord of es:(Name * ASTNode) list
    | EUpdateRec of e0:ASTNode * n:int * e1:ASTNode
    | EAssign of e0:ASTNode
    | EFailWith of n:int
    | EAsm of s:string
    member this.Name =
        match this with
        | EFailWith _
        | ENum _
        | EBool _
        | EStr _ ->
            sprintf "%20A" this
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
    member this.toSExpr () =
        match this.Expr with
        | ENum n -> SNum n
        | EStr s -> SStr s
        | EBool b -> SBool b
        | ENull -> SNull
        | EFailWith n -> SFailWith n
        | EFunc (arg,body) -> SFunc (arg, body.toSExpr ())
        | EVar name -> SVar name
        | EEval e -> SEval (e.toSExpr ())
        | EAp (e1, e2) -> SAp (e1.toSExpr (), e2.toSExpr ())
        | ELet (name, bind, body) -> SLet (name, bind.toSExpr(), body.toSExpr())
        | ELetRec (name, bind, body) -> SLetRec (name, bind.toSExpr(), body.toSExpr())
        | EIf (e0, e1, e2) -> SIf (e0.toSExpr(), e1.toSExpr(), e2.toSExpr())
        | EAdd (e0, e1) -> SAdd (e0.toSExpr(), e1.toSExpr())
        | ESub (e0, e1) -> SSub (e0.toSExpr(), e1.toSExpr())
        | EMul (e0, e1) -> SMul (e0.toSExpr(), e1.toSExpr())
        | EGt (e0, e1) -> SGt (e0.toSExpr(), e1.toSExpr())
        | EEq (e0, e1) -> SEq (e0.toSExpr(), e1.toSExpr())
        | ESelect (e0, e1) -> SSelect (e0.toSExpr(), e1.toSExpr())
        | ERecord es -> SRecord (List.map (fun (name, (e:ASTNode)) -> (name, e.toSExpr())) es)
        | _ -> failwithf "unsupported expr : %A" this.Expr

    static member newId () =
        let id = !currentId
        currentId := id + 1
        id

let mkAST (e:Expr) : ASTNode =
    ASTNode (ASTNode.newId (), e)

let rec toAST sexp : ASTNode =
    match sexp with
    | SFunc (arg, body) -> mkAST (EFunc (arg, toAST body))
    | SEval e -> mkAST (EEval (toAST e))
    | SAp (e1, e2) -> mkAST (EAp (toAST e1, toAST e2))
    | SLet (name, bind, body) -> mkAST (ELet (name, toAST bind, toAST body))
    | SLetRec (name, bind, body) -> mkAST (ELetRec (name, toAST bind, toAST body))
    | SFix e0 -> mkAST (EFix (toAST e0))
    | SIf (e0, e1, e2) -> mkAST (EIf (toAST e0, toAST e1, toAST e2))
    | SAdd (e0, e1) -> mkAST (EAdd (toAST e0, toAST e1))
    | SSub (e0, e1) -> mkAST (ESub (toAST e0, toAST e1))
    | SMul (e0, e1) -> mkAST (EMul (toAST e0, toAST e1))
    | SGt (e0, e1) -> mkAST (EGt (toAST e0, toAST e1))
    | SVar n -> mkAST (EVar n)
    | SNum n -> mkAST (ENum n)
    | SStr s -> mkAST (EStr s)
    | SBool b -> mkAST (EBool b)
    | SNull -> mkAST ENull
    | _ -> failwithf "unexpected term: %A" sexp
