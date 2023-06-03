// For emacs: -*- fsharp -*-

module LHCompiler

// Incomplete pattern matches on this expression.
#nowarn "25"

open System.IO
open Parser
open FSharp.Text.Lexing
open ActorInit
open LHExpr
open LHTypeInfer
open type LHTypes.ProgramTypes
open type LHTypes.Type
type LHType = LHTypes.Type
open type ParserModule.Decl
open type ParserModule.Module

// open type LHTypes.Type

// TODO: put all parse functions into a single module
let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res


type TypeDefs = list<string*LHType>
type ArgList = list<string*option<LHType>>

let rec restoreType (typeDefs:TypeDefs) (arg:LHType) : LHType =
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

let getTypesDeclarationsRaw decls : List<LHTypes.Name * LHType> =
    decls
    |> List.filter (function
                    | TypeDef _ -> true
                    | _         -> false)
    |> List.map (fun n -> n.typeDef)

let getPartiallyDefinedTypes types : List<(LHTypes.Name * LHType) * List<LHTypes.Name>> =
    types  // [(name, typ)]
    |> List.map (fun (name, typ:LHType) ->
                 ((name, typ), LHTypes.hasUndefType typ))
    |> List.filter (fun ((_, _),l) -> l <> [])

let patchPartTypes partTypesNames defs =
    partTypesNames
    |> List.map (fun ((name, typ), undNames) ->
                 // TODO: fixpoint is needed here, because there might
                 // be cyclic references.
                  let rec updateUndName undNames typ =
                     match undNames with
                     | n :: t ->
                        let typ' = LHTypes.insertType n defs typ
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

(**
let patchLetBindingsFuncTypes letBnds types =
    let rec patchLetBodyFuncType (letBody:ASTNode) types =
        match letBody.Expr with
        | EFunc ((argName, Some argType), body) ->
            // patch the argument
            let argType2 = restoreType types argType
            // patch the body
            let body' = patchLetBodyFuncType body types
            mkAST (EFunc ((argName, Some argType2), body'))
        | _ ->
            letBody
    letBnds
    |> List.map ( fun (name, vars, isRec, body) ->
                  (name, vars, isRec, patchLetBodyFuncType body types) )
**)
// "main" or "actorInit" shall be used as finalFunctionName
let rec expandLet finalFunctionName letBind =
    match letBind with
    | [(finalFunctionName, _, false, body)] -> body
    | (name, args, isRec, body) :: t ->
        mkAST (ELet (name, body, expandLet finalFunctionName t))
    | _ -> failwith "incorrect let structure of the program"

let prepareAstWithInitFunction letBnds types  =
    // TODO!!: shall we check main presence as well?
    let actorInitLet =
        letBnds
        |> List.filter (fun (name, _, _, _) -> name = "actorInit")
    if actorInitLet.Length <> 1 then
        failwith "actorInit not found or multiple definitions"
    let (lastLetName, _, _, _) = List.last letBnds
    if (lastLetName <> "actorInit") then
        failwith "actorInit let block shall be the last in the series of let-definitions"
    expandLet "actorInit" letBnds

// Sometimes we may want to compile only the main function, without ActorInit code.
// For example, for tests. This function compiles a set of let bindings with
// types definitions into a big Let-expression.
let prepareAstMain letBnds types =
    let mainLet =
        letBnds
        |> List.filter (fun (name, _, _, _) -> name = "main")
    if mainLet.Length <> 1 then
        failwith "main not found"
    expandLet "main" letBnds

let rec astReducerDebug debug (ast:ASTNode) red =
    match ast.Expr with
    // leaf nodes
    | EVar _
    | ENull
    | EStr _
    | EFailWith _
    | EBool _
    | EAsm _
    | ENum _ ->
        ast
    | ETypeCast (e0, typ) ->
        let e0' = astReducerDebug debug e0 red
        mkAST (ETypeCast (e0', typ))
    | EFunc (arg, body) ->
        let body' = astReducerDebug debug body red
        mkAST (EFunc (arg, body'))
    | ELet (name, bind, body)
    | ELetRec (name, bind, body) ->
        let bind' = astReducerDebug debug bind red
        let body' = astReducerDebug debug body red
        match ast.Expr with
        | ELet _ ->
            mkAST (ELet (name, bind', body'))
        | ELetRec _ ->
            mkAST (ELetRec (name, bind', body'))
    | EIf (e0, e1, e2) ->
        let e0' = astReducerDebug debug e0 red
        let e1' = astReducerDebug debug e1 red
        let e2' = astReducerDebug debug e2 red
        mkAST (EIf (e0', e1', e2'))
    | EAp (e0, e1)
    | EAdd (e0, e1)
    | ESub (e0, e1)
    | EMul (e0, e1)
    | EGt (e0, e1)
    | ELt (e0, e1)
    | EEq (e0, e1)
    | ESelect (e0, e1) ->
        let e0' = astReducerDebug debug e0 red
        let e1' = astReducerDebug debug e1 red
        match ast.Expr with
        | EAp _ -> mkAST (EAp (e0', e1'))
        | EAdd _ -> mkAST (EAdd (e0', e1'))
        | ESub _ -> mkAST (ESub (e0', e1'))
        | EMul _ -> mkAST (EMul (e0', e1'))
        | EGt _ -> mkAST (EGt (e0', e1'))
        | ELt _ -> mkAST (ELt (e0', e1'))
        | EEq _ -> mkAST (EEq (e0', e1'))
        | ESelect _ -> mkAST (ESelect (e0', e1'))
    | ERecord es ->
        es
        |> List.map (fun (name, e) -> (name, astReducerDebug debug e red))
        |> ERecord
        |> mkAST
    | ENot e ->
        mkAST (ENot (astReducerDebug debug e red))
    | _ ->
        failwithf "unrecognised node %A" ast.Expr
    |> (fun ast' ->
        if ast'.toSExpr () = ast.toSExpr () then ast
        else
           if debug then
             printfn "*AR* %s" ((ast'.toSExpr ()).ToString 1000)
           ast'
       )
    |> red

let astReducer (ast:ASTNode) (red: ASTNode -> ASTNode) : ASTNode =
    astReducerDebug false ast red
// eta reduction step:
// (\x -> f x) ==> f
let rec etaStep (node:ASTNode) : ASTNode =
    match node.Expr with
    | EFunc ((argName,argType), body) ->
        match body.Expr with
        | EAp (f, f_arg) ->
            match f_arg.Expr with
            | EVar arg1 when arg1 = argName ->
                etaStep f
            | _ ->
                node
        | _ ->
            let red = etaStep body
            if red = body then node
            else etaStep (mkAST (EFunc ((argName, argType), red)))
    | _ ->
        node

let etaRedex node =
    astReducer node etaStep

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
    | EEq (e1, e2)
    | EAdd (e1, e2)
    | ESub (e1, e2)
    | EMul (e1, e2) ->
        (freeVarsAST e1) @ (freeVarsAST e2)
    | ELet (x, bind, body) ->
        (freeVarsAST bind) @ (freeVarsAST body)
    | ELetRec (x, bind, body) ->
        (freeVarsAST bind) @ (freeVarsAST body)
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

let rec betaRedexStep (node:ASTNode) : ASTNode =
    match node.Expr with
    | ELetRec (x, bind, body) ->
        mkAST (ELetRec (x, betaRedexStep bind, betaRedexStep body))
    | ELet (x, bind, body) ->
        substFreeVar x bind.Expr body
    | EAp (e0, arg) ->
        match e0.Expr with
        | EFunc ((x,_), body) ->
            substFreeVar x arg.Expr body
        | term -> // EAp (EAp (...), arg)
            let node' = betaRedexStep e0
            mkAST (EAp (node', arg))
    | EAdd (e0, e1)
    | EMul (e0, e1)
    | ESub (e0, e1)
    | EEq (e0, e1)
    | ELt (e0, e1)
    | EGt (e0, e1) ->
        let e0' = betaRedexStep e0
        let e1' = betaRedexStep e1
        match node.Expr with
        | EAdd _ -> mkAST (EAdd (e0', e1'))
        | ESub _ -> mkAST (ESub (e0', e1'))
        | EMul _ -> mkAST (EMul (e0', e1'))
        | EGt _ -> mkAST (EGt (e0', e1'))
        | ELt _ -> mkAST (ELt (e0', e1'))
        | EEq _ -> mkAST (EEq (e0', e1'))
    | EIf (e0, e1, e2) ->
        let e0' = betaRedexStep e0
        let e1' = betaRedexStep e1
        let e2' = betaRedexStep e2
        mkAST (EIf (e0', e1', e2'))
    | EVar _
    | EFunc _
    | EBool _
    | ENull
    | EStr _
    | EFailWith _
    | EAsm _
    | ENum _ ->
        node
    | ERecord vs ->  // record instance: [(name,expr)]
        let vs' =
            vs
            |> List.map ( fun (n, e) -> (n, betaRedexStep e) )
        mkAST (ERecord vs')
    | ESelect (ASTNode (_, ERecord vs), ASTNode (_, EVar n)) ->
        Map.ofList vs
        |> Map.tryFind n
        |> function
           | None ->
               failwithf "field %A not found in the record %A" n (node.toSExpr())
           | Some v ->
               mkAST v.Expr
    | ESelect (e0, e1) as e ->
        let e0' = betaRedexStep e0
        // TODO: e1 has to be EVar
        mkAST (ESelect (e0', e1))
    | ETypeCast (e0, typ) ->
        let e0' = betaRedexStep e0
        mkAST (ETypeCast (e0', typ))
    | ENot (e0) ->
        let e0' = betaRedexStep e0
        mkAST (ENot e0')
    | _ ->
        failwithf "Beta Redex for expr %A not defined" node.Expr

let rec betaRedexFullDebug debug node =
    let node' = betaRedexStep node
    if node'.toSExpr () <> node.toSExpr () then
        if debug then
            printfn "*BR* %s" ((node'.toSExpr ()).ToString 1000)
        betaRedexFullDebug debug node'
    else node

// Do redexes until progress stops. We assume that fixpoints
// do not get expanded.
let rec betaRedexFull node =
    betaRedexFullDebug false node

let rec arithSimplRedexDebug debug node =
    let arithSimpl (node : ASTNode) =
        match (node.toSExpr ()) with
        | SAdd (SNum x, SNum y) ->
            mkAST (ENum (x + y))
        | SSub (SNum x, SNum y) ->
            mkAST (ENum (x - y))
        | SMul (SNum x, SNum y) ->
            mkAST (ENum (x * y))
        | SGt (SNum x, SNum y) ->
            mkAST (EBool (x > y))
        | SEq (SNum x, SNum y) ->
            mkAST (EBool (x = y))
        | SEq (SBool x, SBool y) ->
            mkAST (EBool (x = y))
        | SIf (SBool f, x, y) ->
            let (ASTNode (_, EIf (_, tc, fc))) = node
            if f then tc else fc
        | _ ->
            node
    in astReducerDebug debug node arithSimpl


// Here we substitute 'false' letrecs (with no recursion in them),
// for ordinary let expressions; this step has to be done before
// type inference.
let rec letrecRedex node =
    let letrecRedexStep (node:ASTNode) =
        match node.Expr with
        | ELetRec (name, bind, body) ->
            if not (List.exists (fun (ASTNode (_, EVar n)) -> n = name) (freeVarsAST bind)) then
                mkAST (ELet (name, bind, body))
            else node
        | _ ->
            node
    in astReducer node letrecRedexStep

let patchLetBindingsFuncTypes letBnds types =
    let rec patchLetBodyFuncType (letBody:ASTNode) =
        match letBody.Expr with
        | EFunc ((argName, Some argType), body) ->
            // patch the argument
            let argType2 = restoreType types argType
            mkAST (EFunc ((argName, Some argType2), body))
        | _ ->
            letBody
    letBnds
    |> List.map ( fun (name, vars, isRec, body) ->
                  (name, vars, isRec, astReducer body patchLetBodyFuncType) )

//====================================================
// This mutable collection is used not to alter original
// AST with extra nodes. This collection is altered in
// insertEval function, and cleaned after compilation
// completes in compileModule function.
let mutable evalNodes : list<int> = []
//====================================================

let rec insertEval (ast:ASTNode) (env:TypeEnv) (ty:NodeTypeMap) : ASTNode =
    let rec insertEvalInner (node:ASTNode) : ASTNode =
        match node.Expr with
        | EAp (e1, e2) ->
            let t =
                match (Map.tryFind node.Id ty) with
                | Some v -> v
                | None ->
                    failwithf "failed to find type for node %A, expression: %s"
                               node.Id
                               ((ast.toSExpr ()).ToString())
            match t.baseType with
            | LHType.Function _
            | LHType.TVar _ ->
                node
            | _ ->
                // mkAST (EEval node)
                // yes, right. Side-effect, global variable.. gee
                evalNodes <- node.Id :: evalNodes
                node
        | _ ->
            node
    in astReducer ast insertEvalInner

let makeReductions debug (ast:ASTNode) : ASTNode =
    ast
    |> letrecRedex
    |> etaRedex
    |> betaRedexFullDebug debug
    |> arithSimplRedexDebug debug

let compileModule modName decls withInit debug : string =
    if debug then
        printfn "Compiling actor %A" modName ;
    let types = getTypesDeclarationsRaw decls
    let undefTypesNames = getPartiallyDefinedTypes types
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
    let typesFull = defTypes @ completeTypes
    let letBnds = getLetDeclarationsRaw typesFull decls
    let letBndsUpd = patchLetBindingsFuncTypes letBnds typesFull
    if debug then
        printfn "Let Bindings after types patched:\n%A"
                 (letBndsUpd |> List.map (fun (n, args, isrec, body) ->
                                 (n, args, isrec, body.toSExpr ())))
    // TODO!!:
    // Handlers would need to be converted into 'receive' cases in
    // the main function. As for now, they are completely ignored.
    // let handlerDefs = getHandlerDeclsRaw types2 decls
    let finalExpr =
        if withInit then prepareAstWithInitFunction letBndsUpd typesFull
        else prepareAstMain letBndsUpd typesFull
    let ast1 = makeReductions debug finalExpr
    let typeEnv = LHTypeInfer.TypeEnv.ofProgramTypes typesFull
    let (ty, (oldMap, newMap)) =
        LHTypeInfer.typeInferenceDebug
          typeEnv
          ast1
          (Map [])
          debug
    if debug then
        printfn "Nodes type map:\n%A" (Map.toList newMap)
    if debug then
        printfn "Inserting Eval nodes..."
    // We now need to insert EEval nodes in places where
    // continuations are fully saturated and ready to be
    // evaluated into a value (not a partial function).
    insertEval ast1 typeEnv newMap |> ignore // this is done for side-effect only
    if (debug) then
        printfn "Final S-expression:\n%A" (ast1.toSExpr())
    LHMachine.compileWithInitialTypesDebug ast1 newMap evalNodes debug
    |> (fun res ->
            // Clean the eval nodes collection for the next time
            evalNodes <- [] ;
            res)
// The function compiles Lighthouse source code
// into the FIFT source code.
// Arguments:
//  - source = a string representing the source code
//    of an actor.
let compile (source:string) (withInit:bool) (debug:bool) : string =
    let prog = if withInit then (source + ActorInit.actorInitCode)
               else source
    let res = parse prog
    match res with
    | Some (Module (modName, decls)) ->
        compileModule modName decls withInit debug
    | _ ->
        failwith "Actor not found"

// compile Lighthouse source at filePath and output the result (FIFT)
// into the same filePath, but with ".fif" extension
let compileFile (filePath:string) =
    let readFileContents (filePath: string) =
        File.ReadAllText(filePath)
    let replaceFileExtension (filePath: string) =
        let directory = Path.GetDirectoryName(filePath)
        let fileName = Path.GetFileNameWithoutExtension(filePath)
        let newFilePath = Path.Combine(directory, fileName + ".fif")
        newFilePath
    let writeStringToFile (filePath: string) (content: string) =
        File.WriteAllText(filePath, content)
    let fileContent = readFileContents filePath
    let fiftStr = compile fileContent true false
    let newPath = replaceFileExtension filePath
    writeStringToFile newPath fiftStr

// Generate FIFT script that produces .TVC file with
// code and data initialized according to given params.
let generateStateInit outputPath codeFift dataFift : string =
    let newline = System.Environment.NewLine
    "#!/usr/bin/fift -s
\"Asm.fif\" include
{ B>file } : file_write_bytes
{ <b } : builder_begin
{ b> } : builder_end
{ u, } : builder_uint_append
{ ref, } : builder_ref_append
{ boc>B } : cell_to_bytes
{ hashu } : cell_hash
{ x._ } : val_print_hex_ws
{ B>file } : file_write_bytes" + newline +
    "{ " + dataFift + " } : stateinit_data" + newline +
    "{ " + codeFift + " } : stateinit_code" + newline +
    "builder_begin  // b
    0 1  builder_uint_append // b 0 1 -> b'   : split_depth = None
    0 1  builder_uint_append // b 0 1 -> b'   : special = None
    1 1  builder_uint_append // b 1 1 -> b'   : code = Value<Cell>
    1 1  builder_uint_append // b 1 1 -> b'   : data = Value<Cell>
    0 1  builder_uint_append // b 0 1 -> b'   : library = None
    stateinit_code
    builder_ref_append
    stateinit_data
    builder_ref_append" + newline +
    "builder_end dup cell_to_bytes" + newline + "\"" + outputPath +
    "\" file_write_bytes" + newline +
    ".\"0:\" cell_hash val_print_hex_ws"

// Generate FIFT script that produces .BOC file containing
// an external inbound message carrying stateinit with specified
// code and data, and destination address set to that stateinit
// hash.
// let generateMessageWithStateInit outputPath codeFift dataFift : string = ""
