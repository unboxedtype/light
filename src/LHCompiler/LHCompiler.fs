// For emacs: -*- fsharp -*-

module LHCompiler

open System.IO
open Parser
open FSharp.Text.Lexing

open type ParserModule.Decl
open type ParserModule.Module

let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

// The function compiles Lighthouse source code
// into the FIFT source code.
// Arguments:
//  - source = a string representing the source code
//    of an actor.
let compile (source:string) (debug:bool) : string =
    let res = parse source
    match res with
    | Some (Module (modName, decls)) ->
        if debug then
            printfn "Compiling actor %A" modName ;
        let types =
            decls
            |> List.filter (function
                            | TypeDef _ -> true
                            | _ -> false)
            |> List.map (fun n -> n.typeDef)
        if debug then
            printfn "Types found: %A" types
        let letBnds =
            decls
            |> List.filter (function
                            | LetBinding (_, _, _) -> true
                            | _ -> false)
            |> List.map (fun n ->
                         let (name, isRec, expr) = n.letBinding in
                           (name, expr)
                         )
        let handlerDefs =
            decls
            |> List.filter (function
                            | HandlerDef (_, _, _) -> true
                            | _ -> false)
            |> List.map (fun n ->
                         let (name, vars, expr) = n.handlerDef in
                          (name, List.map fst vars, expr))
        // The actor initial state. Currently, empty.
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
            |> List.filter (fun (name, expr) -> name = "main")
        if mainLet.Length <> 1 then
            failwith "main not found"
        let ("main", mainExpr) = List.head mainLet
        LHMachine.compileIntoFift mainExpr
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
    let fiftStr = compile fileContent false
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
    "builder_end
dup
cell_to_bytes
\"" + outputPath + "\" file_write_bytes" + newline +
   ".\"0:\" cell_hash val_print_hex_ws"
