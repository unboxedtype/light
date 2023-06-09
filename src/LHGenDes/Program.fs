open System.IO
open ParserModule

exception AppError of string

let generateReader withInit typeName sourcePath =
    let fileContent = File.ReadAllText sourcePath
    let prog = if withInit then (fileContent + ActorInit.actorInitCode)
               else fileContent
    let res = LHCompiler.parse prog
    match res with
    | Some (Module (modName, decls)) ->
        let typesFull = ParserModule.extractTypes false decls
        let typeMap = Map.ofList typesFull
        if Map.tryFind typeName typeMap = None then
            raise (AppError (typeName + " type not found."))
        let actorStateType = typeMap.[typeName]
        let actorStateReaderCode =
            // without LDCONT support; FIFT doesn't understand it
            LHTypes.deserializeValueSimpl typesFull actorStateType
        actorStateReaderCode
    | _ ->
        failwith "No actor definition found in the file"

[<EntryPoint>]
let main args =
    printfn "Output FIFT script that deserializes Lighthouse Actor state"
    printfn "taken from its blockchain account."
    let argsL = List.ofSeq args
    if List.length argsL <> 2 then
        printfn "USAGE: LHGenDes <pathToSource> <address>"
        1
    else
        let str = generateReader true argsL.[1] argsL.[0]
        TVM.dumpFiftScript "reader.fif" str
        0
