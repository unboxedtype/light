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

// Find all partially defined types within the type term 't'.
let rec hasUndefType (t:Type) : List<Name> =
    match t with
    | UserType (name, None) ->
        List.singleton name
    | UserType (name, Some t) ->
        hasUndefType t
    | PT pts ->
        pts
        |> List.map snd
        |> List.map hasUndefType
        |> List.concat
    | ST sts ->
        sts
        |> List.map snd
        |> List.concat
        |> List.map hasUndefType
        |> List.concat
    | _ ->
        // TODO: what about Function?
        []

let getTypesDeclarationsRaw decls : List<Name * Type> =
    decls
    |> List.filter (function
                    | TypeDef _ -> true
                    | _         -> false)
    |> List.map (fun n -> n.typeDef)

let getPartiallyDefinedTypesNames types : list<(Name*Type)*list<Name>> =
    types  // [(name, typ)]
    |> List.map (fun (name, typ:Type) ->
                 ((name, typ), hasUndefType typ))
    |> List.filter (fun ((_, _),l) -> l <> [])

let getPartiallyDefinedTypes (types : list<Name*Type>) : list<Name*Type> =
    getPartiallyDefinedTypesNames types
    |> List.map fst

type TypeDefs = list<string*Type>
type ArgList = list<string*option<Type>>

let rec restoreType (typeDefs:TypeDefs) (arg:Type) : Type =
    match arg with
    | UserType (n, None) ->   // partially defined type
       let typ =
          match Map.tryFind n (Map.ofList typeDefs) with
          | Some t -> t
          | None -> failwithf "Cant find type definition for type %A" n
       UserType (n, Some typ)
    // TODO: ST type also shall be implemented here.
    | UserType (n, Some t) ->   // restore types in the nested definition
       UserType (n, Some (restoreType typeDefs t))
    | PT pts ->
        pts
        |> List.map ( fun (fn,ft) -> (fn, restoreType typeDefs ft) )
        |> PT
    | Function (t1, t2) ->
        (restoreType typeDefs t1,
         restoreType typeDefs t2)
        |> Function
    | _ ->
        arg

// Returns a list of (name, type) pairs, where partially
// defined types like UserType ("ActorState", None) were
// reconstructed into full types like
// ("ActorState, PT [("balance",Int 256);...])
// based on info from 'types'.
let restoreTypes (typeDefs:TypeDefs) (args:ArgList) : ArgList =
    args
    |> List.map (fun (name, optT) ->
                 match optT with
                 | Some t -> (name, Some (restoreType typeDefs t))
                 | None -> (name, optT)
                )

let patchPartTypes partTypesNames defs : TypeDefs =
    partTypesNames
    |> List.map (fun ((name, typ), undNames) ->
                 // TODO: fixpoint is needed here, because there might
                 // be cyclic references.
                  let rec updateUndName undNames typ =
                     match undNames with
                     | n :: t ->
                        let typ' = insertType n defs typ
                        updateUndName t typ'
                      | [] ->
                         typ
                  (name, updateUndName undNames typ)
                )

// Parser produces collection of declarations. This
// function extracts Let-declarations from this collection
// but also convert it into 'raw' form. i.e. LetBinding (n,...)
// get converted into a tuple (n,...)
let getLetDeclarationsRaw types decls =
    decls
    |> List.collect (function
                     | LetBinding (_, _, _, _) as p -> [p.letBinding]
                     | _ -> [])
    |> List.map ( fun (name, args, isrec, body) ->
                  (name, restoreTypes types args, isrec, body) )

// Same for Handlers. See getLetDeclarationsRaw
let getHandlerDeclsRaw types decls =
    decls
    |> List.collect (function
                     | HandlerDef (_, _, _) as p -> [p.handlerDef]
                     | _ -> [])
    |> List.map ( fun (name, args, body) ->
                  (name, restoreTypes types args, body) )

let extractTypes debug decls =
    let types = getTypesDeclarationsRaw decls
    let undefTypesNames = getPartiallyDefinedTypesNames types
    let undefTypesNamesList =
        undefTypesNames
        |> List.map (fun ((n, _), _) -> n)
    let defTypes =
        types
        |> List.filter (fun (n, t) -> not (List.contains n undefTypesNamesList))
    let completeTypes = patchPartTypes undefTypesNames defTypes
    if debug then
        printfn "Partially defined types:\n%A" undefTypesNames
        printfn "Fully defined types:\n%A" defTypes
        printfn "Completed types:\n%A\n\n" completeTypes
    defTypes @ completeTypes
