// For emacs: -*- fsharp -*-

module Main

open System
open System.IO
open Argu
open LHCompiler

type CliArguments =
    | Input of path:string * dataExpr:string
    | Core of path:string
    // | LightExpr of expr:string
    | AsmOnly
    | Version
    | Debug

    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Input _ -> "Compile a full Light program together with its initial state."
            | Core _ -> "Compile Light Core program from the given file."
            // | LightExpr _ -> "Compile arbitrary Light expression given in a string."
            | AsmOnly -> "Produce .FIFT assembly script and stop."
            | Debug -> "Output all available information during the compilation process (debugging mode)."
            | Version -> "Print compiler version and quit."


let printVersion () =
    printfn "Light (Lighthouse) Compiler Ver.0.0.1 (Venom Hackathon Edition)"

[<EntryPoint>]
let main argv =
    let errorHandler =
        ProcessExiter (colorizer =
                        function
                           | ErrorCode.HelpText -> None
                           | _ -> Some ConsoleColor.Red )
    let parser = ArgumentParser.Create<CliArguments>(programName = "lc",
                                                     errorHandler = errorHandler)
    try
        let results = parser.ParseCommandLine argv
        let debug = results.Contains Debug
        let asmOnly = results.Contains AsmOnly
        if results.Contains Version then
            printVersion () |> ignore
            1
        elif results.Contains Input then
            let (path, dataExpr) = results.GetResult Input
            LHCompiler.compileFile debug asmOnly true path dataExpr |> ignore
            0
        elif results.Contains Core then
            let path = results.GetResult Core
            LHCompiler.compile (File.ReadAllText(path)) false debug
            |> (fun s ->
                use output = System.IO.File.CreateText(path + ".asm")
                fprintf output "\"Asm.fif\" include\n <{ \n %s \n }>s runvmcode .s" s)
            0
        else
            printfn "%s" (parser.PrintUsage()) |> ignore
            1
    with
    | CompilerError s ->
        printfn "Compiler error: %s" s
        1
    | e ->
        printfn "Error: %s" e.Message
        printfn "Source: %s" e.Source
        1
        // printfn "Stack trace: %s..." e.StackTrace
