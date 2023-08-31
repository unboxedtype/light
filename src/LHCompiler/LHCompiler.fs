// For emacs: -*- fsharp -*-

module LHCompiler

// Incomplete pattern matches on this expression.
#nowarn "25"

open System.IO
open Parser
open FSharp.Text.Lexing
open ActorInit
open LHTypeInfer
open LHExpr

open type LHTypes.Type
open type ParserModule.Module

let replaceExt (filePath: string) (newExt: string) =
    let directory = Path.GetDirectoryName (filePath)
    let fileName = Path.GetFileNameWithoutExtension (filePath)
    let newFilePath = Path.Combine(directory, fileName + newExt)
    newFilePath

let onlyName (filePath: string) =
    Path.GetFileNameWithoutExtension (filePath)

// TODO: put all parse functions into a single module
let parse source filename =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

// "main" or "actorInit" shall be used as finalFunctionName
let rec expandLet finalFunctionName letBind =
    match letBind with
    | [(finalFunctionName, _, false, body)] -> body
    | (name, args, false, body) :: t ->
        mkAST (ELet (name, body, expandLet finalFunctionName t))
    | (name, args, true, body) :: t ->
        mkAST (ELetRec (name, body, expandLet finalFunctionName t))
    | _ -> failwith "incorrect let structure of the program"

// Make one big LET expression from global LET-
// definitions. The very last LET experssion is
// the actorInit let block.
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
    | EGtEq (e0, e1)
    | ELtEq (e0, e1)
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
        | EGtEq _ -> mkAST (EGtEq (e0', e1'))
        | ELtEq _ -> mkAST (ELtEq (e0', e1'))
        | ESelect _ -> mkAST (ESelect (e0', e1'))
    | ETuple es ->
        es
        |> List.map (fun e -> astReducerDebug debug e red)
        |> ETuple
        |> mkAST
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

let rec betaRedexStep (node:ASTNode) : ASTNode =
    match node.Expr with
    | ELetRec (x, bind, body) ->
        mkAST (ELetRec (x, betaRedexStep bind, betaRedexStep body))
    | ELet (x, bind, body) ->
        substFreeVar x bind.Expr body
    | EAp (e0, arg) ->
        match e0.Expr with
        | EFunc ((x,_), ASTNode (_, EAsm _)) ->
            node  // do not touch functions containing assembly
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
    | EGt (e0, e1)
    | EGtEq (e0, e1)
    | ELtEq (e0, e1) ->
        let e0' = betaRedexStep e0
        let e1' = betaRedexStep e1
        match node.Expr with
        | EAdd _ -> mkAST (EAdd (e0', e1'))
        | ESub _ -> mkAST (ESub (e0', e1'))
        | EMul _ -> mkAST (EMul (e0', e1'))
        | EGt _ -> mkAST (EGt (e0', e1'))
        | ELt _ -> mkAST (ELt (e0', e1'))
        | EEq _ -> mkAST (EEq (e0', e1'))
        | EGtEq _ -> mkAST (EGtEq (e0', e1'))
        | ELtEq _ -> mkAST (ELtEq (e0', e1'))
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

let rec betaRedexN debug n node =
    if n > 0 then
        let node' = betaRedexStep node
        if node'.toSExpr () <> node.toSExpr () then
            if debug then
                printfn "*BR* %s" ((node'.toSExpr ()).ToString 1000)
            betaRedexN debug (n - 1) node'
        else node
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
            let argType2 = ParserModule.restoreType types argType
            mkAST (EFunc ((argName, Some argType2), body))
        | ETypeCast (node, typ) ->
            let typ' = ParserModule.restoreType types typ
            mkAST (ETypeCast (node, typ'))
        | _ ->
            letBody
    letBnds
    |> List.map ( fun (name, vars, isRec, body) ->
                  (name, vars, isRec, astReducer body patchLetBodyFuncType) )

let makeReductions debug (ast:ASTNode) : ASTNode =
    ast
    |> letrecRedex
    |> etaRedex
//  |> betaRedexFull debug
    |> arithSimplRedexDebug debug

exception CompilerError of string

let compileModule modName decls withInit debug isFift : string =
    if debug then
        printfn "Compiling actor %A" modName ;
    let typesFull = ParserModule.extractTypes debug decls
    if debug then
        File.WriteAllText(modName + ".types", sprintf "%A" typesFull)

    let finalDecls =
        if withInit then
            let typeMap = Map.ofList typesFull
            if Map.tryFind "ActorState" typeMap = None then
                raise (CompilerError "ActorState type not found.")
            let actorStateType = typeMap.["ActorState"]
            let messageBodyType = typeMap.["MessageBody"]
            let actorStateReaderCode =
                LHTypes.deserializeValue typesFull actorStateType
            let actorStateWriterCode =
                LHTypes.serializeValue typesFull actorStateType
            let messageBodyReaderCode =
                (LHTypes.deserializeValueSlice typesFull messageBodyType) @ [TVM.Ends] // " ENDS "
            // pack 5 elements from the stack into a tuple, this will be an
            // ActorInitParams value.
            let aargsLet =
                ParserModule.LetBinding (
                    "actorArgs", [], false,
                    mkAST (
                      ETypeCast (
                         mkAST (EAsm [TVM.Tuple 5]),
                         UserType ("ActorInitArgs", None)
                      )
                    )
                )
            let asrLet =
                ParserModule.LetBinding (
                    // actorStaterReader : VMCell -> ActorState
                    "actorStateReader", [], false,
                    mkAST (
                      EFunc (("x",Some VMCell),
                      mkAST (
                         ETypeCast (
                           mkAST (EAsm actorStateReaderCode),
                           UserType ("ActorState", None))
                         )
                      )
                    )
                )
            let aswLet =
                ParserModule.LetBinding (
                    // actorStaterWriter : ActorState -> VMCell
                    "actorStateWriter", [], false,
                    mkAST (
                      EFunc (
                         ("x", Some (UserType ("ActorState", None))),
                         mkAST (
                           ETypeCast (
                             mkAST (EAsm actorStateWriterCode), VMCell
                           )
                         )
                      )
                   )
                )
            let mbrLet =
                ParserModule.LetBinding (
                // messageBodyReaderSlice : VMSlice -> MessageBody
                    "messageBodyReaderSlice", [], false,
                    mkAST (
                      EFunc (("x",Some VMSlice),
                      mkAST (
                         ETypeCast (
                           mkAST (EAsm messageBodyReaderCode),
                           UserType ("MessageBody", None))
                       )
                      )
                    )
                )
            [aargsLet; asrLet; aswLet; mbrLet] @ decls
        else
            decls
    let letBnds = ParserModule.getLetDeclarationsRaw typesFull finalDecls
    let letBndsUpd = patchLetBindingsFuncTypes letBnds typesFull
    if debug then
        use file0 = System.IO.File.CreateText(modName + ".letbnd")
        fprintfn file0 "%A" (
            letBndsUpd |> List.map (fun (n, args, isrec, body) ->
                                    (n, args, isrec, body.toSExpr ()))
        )


    // TODO!!:
    // Handlers would need to be converted into 'receive' cases in
    // the main function. As for now, they are completely ignored.
    // let handlerDefs = getHandlerDeclsRaw types2 decls
    let finalExpr =
        if withInit then prepareAstWithInitFunction letBndsUpd typesFull
        else prepareAstMain letBndsUpd typesFull
    let ast1 = makeReductions debug finalExpr
    let typeEnv = LHTypeInfer.TypeEnv.ofProgramTypes typesFull
    let debug = false
    let (ty, (oldMap, newMap)) =
        LHTypeInfer.typeInferenceDebug
          typeEnv
          ast1
          (Map [])
          debug

    let ir = LHMachine.compileAST ast1 [] newMap
    let assembly = LHMachine.compileIRIntoAssembly debug isFift ir

    if (debug) then
        use file1 = System.IO.File.CreateText(modName + ".sexpr")
        fprintfn file1 "%A" (ast1.toSExpr())
        use file2 = System.IO.File.CreateText(modName + ".ir")
        fprintfn file2 "%A" ir
        use file3 = System.IO.File.CreateText(modName + ".asm")
        fprintfn file3 "%s" assembly

    assembly

// The function compiles Light source code into the assembly code.
// Arguments:
//  - sourcePath = a string representing the source code path
let compile (sourcePath:string) (withInit:bool) (debug:bool) (isFift:bool) : string =
    if debug then
        printfn "compiling with params: withInit = %A, debug = %A, isFift = %A" withInit debug isFift
    let fileContent = File.ReadAllText sourcePath
    let prog = if withInit then (fileContent + "\n" + ActorInit.actorInitCode)
               else fileContent
    if debug then
       File.WriteAllText(replaceExt sourcePath ".lh.full", prog);
    let res = parse prog sourcePath
    match res with
    | Some (Module (modName, decls)) ->
        if debug then
            File.WriteAllText(modName + ".parse", sprintf "%A" res);
        compileModule modName decls withInit debug isFift
    | _ ->
        failwith "Actor not found"

// Compiles expression into assembly evaluating the
// given expression. Needed to generate init-state and messages
// for actors.
let compileExprOfType (types:list<Name*Type>) exprTypeName exprStr isFift : string =
    let typeMap = Map.ofList types
    if Map.tryFind exprTypeName typeMap = None then
        failwithf "type %A not found" exprTypeName
    let exprT = typeMap.[exprTypeName]
    // TODO! Check type of the expr
    let writerCode =
        LHTypes.serializeValue types exprT
    let writerCodeStr =
        writerCode
        |> List.map (TVM.instructionToAsmString isFift)
        |> String.concat "\n"
    let res1  = parse ("contract Test\nlet main = " + exprStr + " ;; ") "noname"
    let getLetAst (m:ParserModule.Module) (n:int) = m.Decls.[n]
    let letBndMain = getLetAst res1.Value 0
    let fullTypeDecls = types |> List.map ParserModule.TypeDef
    let debug = false
    (compileModule "Test" (fullTypeDecls @ [letBndMain]) false debug isFift) +
      "\n" + writerCodeStr + "\n"

let compileExpr sourcePath exprType exprStr isFift =
    let fileContent = File.ReadAllText sourcePath
    let prog = fileContent + "\n" + ActorInit.actorInitCode
    // File.WriteAllText(sourcePath + ".full", prog)
    let res = parse prog sourcePath
    match res with
    | Some (Module (modName, decls)) ->
        let typesFull = ParserModule.extractTypes false decls
        let typeMap = Map.ofList typesFull
        compileExprOfType typesFull exprType exprStr isFift
    | _ ->
        failwith "No actor definition found in the file"

// Compile Light source located at filePath into .BOC file containing
// a message with the given code and initial data. Data is given in a form
// of a Light expression.
let compileFile (debug:bool) (prodAsm:bool) (withInit:bool) (filePath:string) (dataExpr:string) =
    // 1. Using SDKInterop.executeTVMCode, compile and execute dataExpr, result is stored in Base64
    // 2. Using LHCompiler.compile, compile filePath into Base64
    // 3. Using SDKInterop.encodeStateInit, using (1) data and (2) code, build the stateinit in Base64.
    // 4. Using SDKInterop.encodeInitMsg, using (3), build init message in Base64.
    // 5. Using Convert.FromBase64String, convert (4) into a binary form
    // 6. Using File.WriteAllBytes(path,bytes), store (5) into a file
    let readTextFile (filePath: string) =
        File.ReadAllText(filePath)
    let writeBinaryFile (filePath: string) (content: array<byte>) =
        File.WriteAllBytes(filePath, content)
    let isFift = false
    let dataGenCode = compileExpr filePath "ActorState" dataExpr isFift
    if debug then
        printfn "data expression compiled successfully:"
        printfn "%s" dataGenCode
    let stk = SDKInterop.executeTVMCode SDKInterop.client dataGenCode
    let dataBase64 = stk.[0].GetProperty("value").ToString()
    if debug then
        printfn "Expression value in base64: %s" dataBase64
    let withInit, isFift = true, false
    let codeAsm = compile filePath withInit debug isFift
    if debug then
        File.WriteAllText(replaceExt filePath ".asm", codeAsm);
    if debug then
        printfn "Compiling assembly code into binary (in B64 repr)..."
    let codeBase64 = SDKInterop.compileCode codeAsm
    if debug then
        printfn "Compiling state-init into binary (in B64 repr)..."
    let stateInitBase64 = SDKInterop.encodeStateInit SDKInterop.client codeBase64 dataBase64
    let addr = "0:" + (SDKInterop.accountIdOfStateInit SDKInterop.client stateInitBase64)
    if debug then
        printfn "Actor address is %s" addr
    let initMsgBase64 = SDKInterop.encodeInitMsg SDKInterop.client stateInitBase64
    let initMsgBytes  = System.Convert.FromBase64String (initMsgBase64)
    let bocPath = replaceExt filePath ".boc"
    File.WriteAllBytes (bocPath, initMsgBytes) ;
