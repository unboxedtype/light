#!/usr/bin/env -S dotnet fsi

#r "FsLexYacc.Runtime.dll"
#r "FiftExecutor.dll" ;;
#r "LHTypes.dll" ;;
#r "Parser.dll" ;;
#r "LHExpr.dll" ;;
#r "TVM.dll" ;;
#r "LHMachine.dll" ;;
#r "LHCompiler.dll" ;;
open FSharp.Text.Lexing ;;
open LHTypes ;;
open Parser ;;
open ParserModule ;;
open LHExpr ;;
open LHCompiler ;;
open System ;;
open System.IO ;;

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  Parser.start Lexer.read lexbuf ;;

let constrFiftPath = "./exprConstr.fif"
let constrTvcPath = "./exprConstr.tvc"

let executeConstrCode () =
    let res = FiftExecutor.executeShellCommand "fift" constrFiftPath
    if res.ExitCode <> 0 then
        failwithf "Command executed with an error: %s; output: %s"
                  res.StandardError
                  res.StandardOutput

let extractBoc tvcPath =
    // now we need to extract data from exprConstr.tvc. That
    // will be our message object serialized into .boc.
    let res = FiftExecutor.executeShellCommand "extractData.sh" (tvcPath + " data.boc")
    if res.ExitCode <> 0 then
        failwithf "Command executed with an error: %s; output: %s"
                  res.StandardError
                  res.StandardOutput


let compileExpr sourcePath exprType exprStr =
    let fileContent = File.ReadAllText sourcePath
    let prog = fileContent + ActorInit.actorInitCode
    let res = LHCompiler.parse prog
    match res with
    | Some (Module (modName, decls)) ->
        let typesFull = ParserModule.extractTypes false decls
        let typeMap = Map.ofList typesFull
        compileExprOfType typesFull exprType exprStr
    | _ ->
        failwith "No actor definition found in the file"

// Run FIFT with the construction script, so we have msg_constr.boc ready
// to be executed by tvm_linker
let assembleConstrBoc () =
    let res = FiftExecutor.executeShellCommand "fift" constrFiftPath
    if res.ExitCode <> 0 then
        failwithf "Command executed with an error: %s; output: %s"
                  res.StandardError
                  res.StandardOutput

let executeConstrBoc tvcPath =
    let res = FiftExecutor.executeShellCommand "tvm_linker" ("test " + tvcPath)
    if res.ExitCode <> 0 then
        failwithf "Command executed with an error: %s; output: %s"
                  res.StandardError
                  res.StandardOutput

// sourcePath = path to the receiver-actor source code
// destId = a unique identifier of the destination actor
// exprStr = an expression written in Light language that will become
// the message body. For example '{ seqNo = 100; { n = 20 } }' in case
// the contract message type is 'ActorMessage = { n : int }'. SeqNo must increase
// with each new message. The actual seqNo can be inspected by
// getActorState.sh
let generateExprBoc sourcePath exprType exprStr =
    "<{ " + (compileExpr sourcePath exprType exprStr) + " c4 POP }>s s>c "
    |> (fun code -> TVM.genStateInit constrTvcPath code "<b b>")
    |> TVM.dumpFiftScript constrFiftPath
    assembleConstrBoc () |> ignore ;
    executeConstrBoc constrTvcPath |> ignore ;
    extractBoc constrTvcPath

let args = List.ofSeq (System.Environment.GetCommandLineArgs())
if List.length args <> 5 then
    printfn "This script serializes arbitrary Light expression result into BOC"
    printfn ""
    printfn "USAGE: serializeExpression.fsx <pathToSource> <expressionType> <expression>"
    exit 1
let sourcePath = args.[2]
let exprType = args.[3]
let exprStr = args.[4]

generateExprBoc sourcePath exprType exprStr
