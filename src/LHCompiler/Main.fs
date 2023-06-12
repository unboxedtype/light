// For emacs: -*- fsharp -*-

module Main

open System
open Argu
open LHCompiler

type CliArguments =
    | Input of path:string * dataExpr:string
    | Version
    | Verbose

    interface IArgParserTemplate with
        member s.Usage =
            match s with
            | Input _ -> "Compile a Light program. Initial state given in a form of Light expression. It has to be a value of the ActorState type."
            | Verbose -> "Turn on verbose compilation (Mostly for compiler debugging)."
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
        if results.Contains Version then
            printVersion () |> ignore
            1
        elif results.Contains Input then
            let (path, dataExpr) = results.GetResult Input
            let debug = results.Contains Verbose
            LHCompiler.compileFile debug path dataExpr |> ignore
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
