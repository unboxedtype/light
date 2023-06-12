#!/usr/bin/env -S dotnet fsi

#r "../src/LHCompiler/bin/Debug/net6.0/FsLexYacc.Runtime.dll"
#r "../src/FiftExecutor/bin/Debug/net6.0/FiftExecutor.dll" ;;
#r "../src/LHCompiler/bin/Debug/net6.0/LHTypes.dll" ;;
#r "../src/LHCompiler/bin/Debug/net6.0/Parser.dll" ;;
#r "../src/LHCompiler/bin/Debug/net6.0/LHExpr.dll" ;;
#r "../src/LHCompiler/bin/Debug/net6.0/TVM.dll" ;;
#r "../src/LHCompiler/bin/Debug/net6.0/LHMachine.dll" ;;
#r "../src/LHCompiler/bin/Debug/net6.0/LHCompiler.dll" ;;
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

let constrFiftPath = "./expr_constr.fif"
let constrTvcPath = "./expr_constr.tvc"

let executeConstrCode () =
    if (FiftExecutor.runFiftScript constrFiftPath) = "empty" then
        failwithf "Fift executed the script %s with an error" constrFiftPath
    else
        ()

let extractBoc tvcPath =
    // now we need to extract data from msg_constr.boc. That
    // will be our message object serialized into .boc.
    FiftExecutor.executeShellCommand "extractData.sh" (tvcPath + " data.boc")

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
    FiftExecutor.executeShellCommand "fift" constrFiftPath

let executeConstrBoc tvcPath =
    FiftExecutor.executeShellCommand "tvm_linker" ("test " + tvcPath)

// sourcePath = path to the receiver-actor source code
// destId = a unique identifier of the destination actor
// exprStr = an expression written in Light language that will become
// the message body. For example '{ seqNo = 100; { n = 20 } }' in case
// the contract message type is 'ActorMessage = { n : int }'. SeqNo must increase
// with each new message. The actual seqNo can be inspected by
// getActorState.sh
let generateExprBoc sourcePath exprType exprStr =
    "<{ " + (compileExpr sourcePath exprType exprStr) + "}>s s>c "
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
