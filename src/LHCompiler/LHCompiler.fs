// For emacs: -*- fsharp -*-

module LHCompiler

open Parser
open FSharp.Text.Lexing
open type ParserModule.Decl
open type ParserModule.Module

let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

let compile s =
    let res = parse s
    match res with
    | Some (Module (modName, decls)) ->
        printfn "Compiling contract %A" modName ;
        let types =
            decls
            |> List.filter (function
                            | TypeDef _ -> true
                            | _ -> false)
            |> List.map (fun n -> n.unboxTypeDef)
        let types' = types @ [("state", LHTypes.UserType "State")]
        let letBnds =
            decls
            |> List.filter (function
                            | LetBinding (_, _, _) -> true
                            | _ -> false)
            |> List.map (fun n ->
                         let (name, isRec, expr) = n.unboxLetBinding in
                           (name, [], expr)
                         )
        let handlerDefs =
            decls
            |> List.filter (function
                            | HandlerDef (_, _, _) -> true
                            | _ -> false)
            |> List.map (fun n ->
                         let (name, vars, expr) = n.unboxHandlerDef in
                          (name, List.map fst vars, expr))
        let globals = [("state", [], LHMachine.ENull)] @ letBnds @ handlerDefs
        let lhGlobalsTable = LHMachine.compileGlobalsWithTypes globals types'
        let dataCellContent = "<b b>"
        let stReader =
            LHTypes.stateReader types'
            |> List.map TVM.instrToFift
            |> String.concat "\n"
        let stWriter =
            LHTypes.stateWriter types'
            |> List.map TVM.instrToFift
            |> String.concat "\n"        
        LHMachine.generateFift lhGlobalsTable stReader stWriter dataCellContent
    | _ ->
        failwith "Contract not found"
