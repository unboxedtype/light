// For emacs: -*- fsharp -*-

module LHTypeInfer

open System

open LHTypes
open type LHMachine.Expr

type name = string
type label = string

type exp =
    LHMachine.Expr

type Typ = LHTypes.Type

type Scheme = Scheme of name list * Typ
type TypeEnv = Map<string, Scheme>
type Subst = Map<name,Typ>

// Map.union is missing? This is just a throw-away stub
let mapUnion m1 m2 =
    let l1 = Map.toList m1
    let l2 = Map.toList m2
    Map.ofList (l1 @ l2)

let mapSingleton k v =
    Map.ofList ([k, v])

module Typ =
    let rec ftv (typ: Typ) =
        match typ with
        | TVar name -> Set.singleton name
        | Int _
        | Unit
        | String
        | Bool -> Set.empty
        | Function (t1, t2) -> Set.union (ftv t1) (ftv t2)
        | _ -> failwithf "type %A is not supported" typ

    // apply substitution s to type t.
    // basically, it is about substituting type variables
    // with discovered types stored in s.
    let rec apply s typ : Typ =
        match typ with
        | TVar n ->
            match Map.tryFind n s with
            | Some t -> t
            | None -> TVar n
        | Function (t1, t2) ->
            Function (apply s t1, apply s t2)
        | Int _
        | Bool
        | Unit ->
            typ
        | _ -> failwithf "type %A is not supported" typ

    let parens s =
        sprintf "( %s )" s

    let braces s =
        sprintf "{ %s }" s
    let rec toString ty =
        let rec parenType ty =
            match ty with
            |  Function (_type1, _type2) -> parens (toString ty)
            | _ -> toString ty

        match ty with
            | TVar name -> name
            | Int n -> "int" + (string n)
            | Bool -> "bool"
            | Function (t, s) ->
                "(" + (parenType t) + " -> " + (toString s) + ")"
            | _ ->
                failwithf "type %A is not supported" ty

module Scheme =
   let ftv (scheme: Scheme) =
       match scheme with
       | Scheme(variables, typ) ->
           Set.difference (Typ.ftv typ) (Set.ofList variables)

   let apply (s: Subst) (scheme: Scheme) =
       match scheme with
       | Scheme(vars, t) ->
           let newSubst = List.foldBack (fun key currentSubst -> Map.remove key currentSubst ) vars s
           let newTyp = Typ.apply newSubst t
           Scheme(vars, newTyp)

module TypeEnv =
     let remove (env: TypeEnv) (var : string)=
         Map.remove var env
     let ftv (typEnv: TypeEnv) =
        Seq.foldBack (fun (KeyValue(_key ,v)) state ->
            Set.union state (Scheme.ftv v)) typEnv Set.empty
     let apply (s : Subst) (env: TypeEnv) : TypeEnv =
        Map.map (fun _k v -> Scheme.apply s v) env

module Subst =
    /// Apply `s1` to `s2` then merge the results
    let compose s1 s2 =
        mapUnion s1 (Map.map (fun _k (v : Typ) -> Typ.apply s1 v) s2)

///generalize abstracts a type over all type variables which are free
/// in the type but not free in the given type environment.
let generalize (env : TypeEnv) (t : Typ) =
    let variables =
       Set.difference (Typ.ftv t) (TypeEnv.ftv env)
       |> Set.toList
    Scheme(variables, t)

let private currentId = ref 0

let nextId() =
    let id = !currentId
    currentId := id + 1
    id

let resetId() = currentId := 0

let newTyVar prefix =
    TVar ( sprintf "%s%i" prefix (nextId ()))

/// Replaces all bound type variables in a type scheme with fresh type variables.
let instantiate (ts : Scheme) =
    match ts with
    | Scheme(vars, t) ->
        let nvars = vars |> List.map (fun name -> newTyVar (string name.[0]) )
        let s = List.zip vars nvars |> Map.ofList
        Typ.apply s t

let varBind u t =
    match t with
    | TVar name when name = u -> Map.empty
    | _ when Set.contains u (Typ.ftv t) ->
        failwithf "Occur check fails: %s vs %A" u t
    | _ -> Map.ofList [(u, t)]

let rec unify (t1 : Typ) (t2 : Typ) : Subst =
    match t1, t2 with
    | Function (l, r), Function (l', r') ->
        let s1 = unify l l'
        let s2 = unify (Typ.apply s1 r) (Typ.apply s1 r')
        Subst.compose s2 s1
    | TVar u, t
    | t, TVar u -> varBind u t
    | Int n, Int m when n = m -> Map.empty
    | Bool, Bool -> Map.empty
    | _ -> failwithf "Types do not unify: %A vs %A" t1 t2

let rec ti (env : TypeEnv) (exp : exp) : Subst * Typ =
    match exp with
    | ENum n ->
        printfn "%A : s' = %A" exp.Name Map.empty
        (Map.empty, Int 256)
    | ENull  ->
        printfn "%A : s' = %A" exp.Name Map.empty
        (Map.empty, Unit)
    | EVar name ->
        match Map.tryFind name env with
        | None ->
            failwithf "Unbound variable: %s" name
        | Some sigma ->
            let t = instantiate sigma
            printfn "%A : s' = %A" exp.Name Map.empty
            (Map.empty, t)
    | EAdd (e1, e2)
    | EMul (e1, e2)
    | ESub (e1, e2) ->
        // The '+' operator impose constraints on its arguments,
        // both of them must be Integers.
        let s1, t1 = ti env e1
        let s2, t2 = ti env e2
        let st1 = unify t1 (Int 256)
        let st2 = unify t2 (Int 256)
        let s' = Subst.compose (Subst.compose s1 s2) (Subst.compose st1 st2)
        printfn "%A : s' = %A" exp.Name  s'
        (s', Int 256)
    | EFunc (n, e) ->
        let tv = newTyVar "a"
        let env1 = TypeEnv.remove env n
        let env2 = mapUnion env1 (mapSingleton n (Scheme([], tv) ))
        let (s', t1) = ti env2 e
        printfn "%A : s' = %A" exp.Name  s'
        (s', Function (Typ.apply s' tv, t1))
    | EAp (e1, e2) ->
        let s1, t1 = ti env e1
        let s2, t2 = ti (TypeEnv.apply s1 env) e2
        let tv = newTyVar "a"
        let s3 = unify (Typ.apply s2 t1) (Function (t2, tv))
        let s' = Subst.compose s3 (Subst.compose s2 s1)
        printfn "%A : s' = %A" exp.Name  s'
        (s', Typ.apply s3 tv)
    | EIf (cond, e1, e2) ->
        let t' = newTyVar "a"       // if expression type, fresh var
        let sc, tc = ti env cond
        let s1, t1 = ti env e1
        let s2, t2 = ti env e2
        let scond = unify tc Bool   // Conditional must be a boolean.
        let s1' = unify (Typ.apply scond t1) (Typ.apply scond t2)
        // The type of if branch must equal the type of else branch.
        let s2' = unify t' t1
        let s3' = unify t' t2
        let s' = Subst.compose scond
                  (Subst.compose (Subst.compose sc s1')
                                 (Subst.compose
                                   (Subst.compose s1 s2)
                                   (Subst.compose s2' s3')))
        printfn "%A : s' = %A" exp.Name  s'
        (s', t')
    | ELet (x, e1, e2) ->
        let s1, t1 = ti env e1
        let env1 = TypeEnv.remove env x
        let scheme = generalize (TypeEnv.apply s1 env) t1
        let env2  =  Map.add x scheme env1
        let s2, t2 = ti (TypeEnv.apply s1 env2 ) e2
        let s' = Subst.compose s2 s1
        printfn "%A : s' = %A" exp.Name  s'
        (s', t2)
    | ELetRec (x, e1, e2) ->
        let (s', t') = ti env (ELet (x, EFix (EFunc (x, e1)), e2))
        printfn "%A : s' = %A" exp.Name  s'
        (s', t')
    | EFix e ->
        let (s', t) = ti env e
        // printfn "%A : t = %A, s' = %A, env = %A" exp.Name t s' env
        let t' =
          match (Typ.apply s' t) with
          | Function (t1, t2) when t1 = t2 -> t1
          | _ ->
              failwithf "Unexpected type for a fix point argument: %A" t
        printfn "%A : s' = %A" exp.Name  s'
        (s', t')
    | EGt (e1, e2) ->
        let s1, t1 = ti env e1
        let s2, t2 = ti env e2
        let s1' = unify t1 (Int 256)
        let s2' = unify t2 (Int 256)
        let s' = Subst.compose (Subst.compose s1 s2) (Subst.compose s1' s2')
        printfn "%A : s' = %A" exp.Name  s'
        (s', Bool)
    | _ ->
        failwithf "Unsupported expression %A" exp

let typeInference env e =
  let s, t = ti env e
  printfn "t = %A, s = %A" t s
  Typ.apply s t
