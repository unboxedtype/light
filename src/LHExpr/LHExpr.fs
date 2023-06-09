// For emacs: -*- fsharp -*-

// Lighthouse language AST node type.
// Here, the AST is untyped. We supply type for each
// node somewhere else.

module LHExpr

open type LHTypes.Type

// global counter for generating new AST IDs
let private currentId = ref 0

type Type = LHTypes.Type

type Name = string

// Simplified Expression. This variant is more suitable
// for testing purposes, while ASTNode is for real compilation.
type SExpr =
    | SNum of n:int                     // value of type Int
    | SStr of s:string
    | SBool of b:bool
    | SNull                             // value Null (unit)
    | SFunc of arg:(Name*option<Type>) * body:SExpr     // value of type Function<T1,T2>
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
    | SLt of e0:SExpr * e1:SExpr
    | SGtEq of e0:SExpr * e1:SExpr
    | SLtEq of e0:SExpr * e1:SExpr
    | SNot of e0:SExpr
    | SCase of c:SExpr * cs:(int * (Name list) * SExpr) list
    | SPack of tag:int * arity:int * args:SExpr list
    | SSelect of e0:SExpr * e1:SExpr
    | SRecord of es:(Name * SExpr) list
    | SUpdateRec of e0:SExpr * n:int * e1:SExpr
    | SAssign of e0:SExpr
    | SAsm of s:string
    | STypeCast of e1:SExpr * typ:Type
    | SFailWith of n:int
    member this.ToString n =
        let s = sprintf "%A" this
        let len = s.Length
        let newlen = min n len
        s.Substring (0, newlen) + (if (len > n) then "..." else "")
    override this.ToString () =
        this.ToString 200

// AST Expression
type Expr =
    | ENum of n:int                     // value of type Int
    | EStr of s:string                  // value of type String
    | EBool of b:bool
    | ENull                             // value Null (Unit)
    | ETuple of list<ASTNode>
    | EFunc of arg:(Name*option<Type>) * body:ASTNode  // value of type Function<T1,T2>
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
    | ELt of e0:ASTNode * e1:ASTNode
    | EGtEq of e0:ASTNode * e1:ASTNode
    | ELtEq of e0:ASTNode * e1:ASTNode
    | ENot of e0:ASTNode
    | ECase of c:ASTNode * cs:(int * (Name list) * ASTNode) list
    | EPack of tag:int * arity:int * args:ASTNode list
    | ESelect of e0:ASTNode * e1:ASTNode
    | ERecord of es:(Name * ASTNode) list
    | EUpdateRec of e0:ASTNode * n:int * e1:ASTNode
    | EAssign of e0:ASTNode
    | EFailWith of n:int
    | EAsm of s:string
    | ETypeCast of e0:ASTNode * typ:Type
    member this.Name =
        match this with
        | EFailWith _
        | ENum _
        | EBool _
        | EAsm _
        | EStr _ ->
            sprintf "%A" this
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
        | ELt (_, _) -> "ELt"
        | ENot (_) -> "ENot"
        | EEq (_, _) -> "EEq"
        | EFix _ -> "EFix"
        | ETypeCast (_, _) -> sprintf "%A" this
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
        | ELt (e0, e1) -> SLt (e0.toSExpr(), e1.toSExpr())
        | EGtEq (e0, e1) -> SGtEq (e0.toSExpr(), e1.toSExpr())
        | ELtEq (e0, e1) -> SLtEq (e0.toSExpr(), e1.toSExpr())
        | ENot (e0) -> SNot (e0.toSExpr())
        | ESelect (e0, e1) -> SSelect (e0.toSExpr(), e1.toSExpr())
        | ERecord es -> SRecord (List.map (fun (name, (e:ASTNode)) -> (name, e.toSExpr())) es)
        | EAsm s -> SAsm s
        | ETypeCast (e0, typ) -> STypeCast (e0.toSExpr(), typ)
        | EFix e0 -> SFix (e0.toSExpr())
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
    | SLt (e0, e1) -> mkAST (ELt (toAST e0, toAST e1))
    | SLtEq (e0, e1) -> mkAST (ELtEq (toAST e0, toAST e1))
    | SGtEq (e0, e1) -> mkAST (EGtEq (toAST e0, toAST e1))
    | SNot (e0) -> mkAST (ENot (toAST e0))
    | SVar n -> mkAST (EVar n)
    | SNum n -> mkAST (ENum n)
    | SStr s -> mkAST (EStr s)
    | SBool b -> mkAST (EBool b)
    | SNull -> mkAST ENull
    | SAsm s -> mkAST (EAsm s)
    | STypeCast (e0, typ) -> mkAST (ETypeCast (toAST e0, typ))
    | _ -> failwithf "unexpected term: %A" sexp

// Find all free variables (i.e. nodes of type (EVar n)) inside the
// given AST node. Return found nodes in a list form.
let rec freeVarsAST (ast:ASTNode) : ASTNode list =
    match ast.Expr with
    | ENull
    | ENum _
    | EAsm _
    | EFailWith _
    | EBool _ -> []
    | EVar x -> List.singleton ast
    | ETypeCast (expr, _) ->
        freeVarsAST expr
    | ENot expr ->
        freeVarsAST expr
    | EFunc ((argName, _), body) ->
        freeVarsAST body
        |> List.filter (fun (ASTNode (_, EVar n)) -> n <> argName)   //List.except [y]
    | EAp (e1, e2)
    | EGt (e1, e2)
    | ELt (e1, e2)
    | EGtEq (e1, e2)
    | ELtEq (e1, e2)
    | EEq (e1, e2)
    | EAdd (e1, e2)
    | ESub (e1, e2)
    | EMul (e1, e2) ->
        (freeVarsAST e1) @ (freeVarsAST e2)
    | ELet (x, bind, body) ->
        (freeVarsAST bind) @
        (freeVarsAST body
         |> List.filter (fun (ASTNode (_, EVar n)) -> n <> x) )
    | ELetRec (x, bind, body) ->
        (freeVarsAST bind) @
        (freeVarsAST body
         |> List.filter (fun (ASTNode (_, EVar n)) -> n <> x) )
    | EIf (e1, e2, e3) ->
        (freeVarsAST e1) @ (freeVarsAST e2) @ (freeVarsAST e3)
    | ERecord vs ->
        vs
        |> List.map snd
        |> List.map freeVarsAST
        |> List.concat
    | ESelect (e0, e1) ->
        freeVarsAST e0
    | _ ->
        failwithf "freeVars for %20A not implemented" ast.Expr

// global counter for generating unique variable names
let private nameId = ref 0

// Substitute a free variable 'x' for the term y in the 'node'
let rec substFreeVar (x:string) (y:Expr) (node:ASTNode) : ASTNode =
    let newVarName () =
        let id = !nameId
        nameId := id + 1 ;
        "z" + (string id)
    match node.Expr with
    | EVar x' ->
        if x' = x then mkAST y
        else node
    | ENum _
    | EBool _
    | EAsm _
    | ENull ->
        node
    | EGt (e0, e1)
    | ELt (e0, e1)
    | EGtEq (e0, e1)
    | ELtEq (e0, e1)
    | ESub (e0, e1)
    | EMul (e0, e1)
    | EAdd (e0, e1)
    | EEq (e0, e1)
    | EAp (e0, e1) ->
        let e0' = substFreeVar x y e0
        let e1' = substFreeVar x y e1
        mkAST ( match node.Expr with
                | EGt _ -> EGt (e0', e1')
                | EEq _ -> EEq (e0', e1')
                | ELt _ -> ELt (e0', e1')
                | EGtEq _ -> EGtEq (e0', e1')
                | ELtEq _ -> ELtEq (e0', e1')
                | ESub _ -> ESub (e0', e1')
                | EMul _ -> EMul (e0', e1')
                | EAdd _ -> EAdd (e0', e1')
                | EAp _ -> EAp (e0', e1')
              )
    | ETypeCast (e0, typ) ->
        mkAST (ETypeCast (substFreeVar x y e0, typ))
    | ENot (e0) ->
        mkAST (ENot (substFreeVar x y e0))
    | EIf (e0, e1, e2) ->
        mkAST (EIf (substFreeVar x y e0,
                    substFreeVar x y e1,
                    substFreeVar x y e2))
    | EFunc ((argName,_), body) when argName = x ->
        node
    | EFunc ((name,typ), body) ->  // here name <> x
        let yFreeVars = freeVarsAST (mkAST y)
        if List.exists (fun (ASTNode (_, EVar n)) -> n = name) yFreeVars then
            let z = newVarName ()
            let newBody = substFreeVar name (EVar z) body
            mkAST (EFunc ((z,typ), substFreeVar x y newBody))
        else
            mkAST (EFunc ((name,typ), substFreeVar x y body))
    | ELet (arg, bind, body) ->
        mkAST (ELet (arg, substFreeVar x y bind, substFreeVar x y body))
    | ELetRec (arg, bind, body) ->
        mkAST (ELetRec (arg, substFreeVar x y bind, substFreeVar x y body))
    | ERecord es ->
        let es' = List.map (fun (name, term) -> (name, substFreeVar x y term)) es
        mkAST (ERecord es')
    | ESelect (e0, e1) ->
        mkAST (ESelect ((substFreeVar x y e0), e1))
    | EFailWith _ ->
        node
    | _ ->
        failwithf "substFreeVar not implemented for %A" node.Expr
