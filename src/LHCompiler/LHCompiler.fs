// For emacs: -*- fsharp -*-

module LHCompiler

open System.IO
open Parser
open FSharp.Text.Lexing
open ActorInit
open LHExpr

open type ParserModule.Decl
open type ParserModule.Module
open type LHTypes.Type

// TODO: put all parse functions into a single module
let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

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
        if debug then
            printfn "Compiling actor %A" modName ;
        let types : List<LHTypes.Name * LHTypes.Type> =
            decls
            |> List.filter (function
                            | TypeDef _ -> true
                            | _         -> false)
            |> List.map (fun n -> n.typeDef)
        let undefTypesNames : List<(LHTypes.Name * LHTypes.Type) * List<LHTypes.Name>> =
            types  // [(name, typ)]
            |> List.map (fun (name, typ:LHTypes.Type) ->
                         ((name, typ), LHTypes.hasUndefType typ))
            |> List.filter (fun ((_, _),l) -> l <> [])
        let undefTypesNamesList =
            undefTypesNames
            |> List.map (fun ((n, _), _) -> n)
        if debug then
            printfn "Partially defined types:\n%A" undefTypesNames
        let defTypes =
            types
            |> List.filter (fun (n, t) -> not (List.contains n undefTypesNamesList))
        if debug then
            printfn "Fully defined types:\n%A" defTypes
        let completeTypes =
            undefTypesNames
            |> List.map (fun ((name, typ), undNames) ->
                         // TODO: fixpoint is needed here, because there might
                         // be cyclic references.
                         let rec updateUndName undNames typ =
                            match undNames with
                            | n :: t ->
                               let typ' = LHTypes.insertType n defTypes typ
                               updateUndName t typ'
                            | [] ->
                               typ
                         (name, updateUndName undNames typ))
        if debug then
            printfn "Completed types:\n%A" completeTypes
        let types2 = defTypes @ completeTypes
        let letBnds =
            decls
            |> List.filter (function
                            | LetBinding (_, _, _, _) -> true
                            | _ -> false)
            |> List.map (fun n -> n.letBinding)   // (name,vars,isRec,body)
        let handlerDefs =
            decls
            |> List.filter (function
                            | HandlerDef (_, _, _) -> true
                            | _ -> false)
            |> List.map (fun n ->
                         let (name, vars, expr) = n.handlerDef in
                          (name, List.map fst vars, expr))
        // The actor initial state. Currently, empty.
        // For debugging.
        let dataCellContent = "<b b>"

        (**
        // State deserializer.
        let stReader =
            LHTypes.stateReader types
            |> List.map TVM.instrToFift
            |> String.concat "\n"

        // State serializer.
        let stWriter =
            LHTypes.stateWriter types
            |> List.map TVM.instrToFift
            |> String.concat "\n"
        **)
        let mainLet =
            letBnds
            |> List.filter (fun (name, _, _, _) -> name = "main")
        if mainLet.Length <> 1 then
            failwith "main not found"
        let ("main", _, _, mainExpr) = List.head mainLet
        let finalExpr =
            if withInit then
                let actorInitLet =
                   letBnds
                   |> List.filter (fun (name, _, _, _) -> name = "actorInit")
                if actorInitLet.Length <> 1 then
                    failwith "actorInit not found or multiple definitions"
                let (lastLetName, _, _, _) = List.last letBnds
                if (lastLetName <> "actorInit") then
                    failwith "actorInit let block shall be the last in the series of let-definitions"
                // Now we need to prepare knownVariableTypes mapping: together with type definitions,
                // it constitutes our initial type information.
                // To prepare the mapping, we:
                // 1. Collect NodeId's of let arguments inside the expression body (where they are used free),
                    // in a form of List<ASTNode(nodeId, EVar varName)>
                // 2. Match those with types given in let expression (varName, varType),
                    // resulting in List<(nodeId, varType)> pairs
                // 3. Convert the list into a mapping
                // 4. Pass this mapping further to LHMachine
                let collectNodeIds letExpr varName : List<int> =
                   []
                // Fold global Let bindings one into another, so we have a
                // complete program definition with actorInit being the very
                // last expression.
                let ("actorInit", _, _, actorInitLetBinding) :: other = List.rev letBnds
                let astNode =
                    List.fold (fun acc (name, _, _, expr) ->
                               mkAST (ELet (name, expr, acc))) actorInitLetBinding other
                astNode
            else
                // Sometimes we may want to compile only the main function, without ActorInit code.
                // For example, for tests.
                mainExpr
        let nodeTypeMapping = Map []
        if (debug) then
            printfn "Final expression:\n%A" ((finalExpr.toSExpr()).ToString(1000))
        LHMachine.compileWithInitialTypesDebug finalExpr types2 nodeTypeMapping debug
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
