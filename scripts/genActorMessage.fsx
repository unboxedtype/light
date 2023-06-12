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

let executeMsgConstrCode () =
    if (FiftExecutor.runFiftScript "./msg_constr.fif") = "empty" then
        failwithf "Fift executed the script %s with an error" "msg_constr.fif"
    else
        ()

let extractMsgBoc tvcPath =
    // now we need to extract data from msg_constr.boc. That
    // will be our message object serialized into .boc.
    FiftExecutor.executeShellCommand "extractData.sh" (tvcPath + " msg.boc")

let generateMsgConstructorCode destId msgBodyCode =
    "5 BLKDROP\n" +  // remove TVM shit from the stack
    msgBodyCode + "\n" +
    // Here, we have data cell serialized on the stack
    // Now we need to generate the whole Message boc, and put it into C4
    "2 INT   // ext_in_msg_info constructor tag
     0 INT   // src: addrNone tag
     2 INT   // dest: MsgAddressInt tag
     0 INT   // no anycast
     0 INT   // workchain 0
    " +
    (destId + " INT // destination address \n") +
    "0 INT   // import_fee = 0
     0 INT   // no state init
     1 INT   // data is provided as a cell
     s9 PUSH // data cell
     10 0 REVERSE  // serialize in the opposite order
     NEWC
     2 STU   // ext_in_msg_info constructor
     2 STU   // src: addrNone tag
     2 STU   // dest: addrStd tag
     1 STU   // no anycast
     8 STU   // workchain id
     256 STU // actor id
     4 STU   // import fee
     1 STU   // state init presence flag
     1 STU   // body presence flag
     STREF   // body cell
     ENDC
     c4 POP"

let compileMessageBody sourcePath exprStr =
    let fileContent = File.ReadAllText sourcePath
    let prog = fileContent + ActorInit.actorInitCode
    let res = LHCompiler.parse prog
    match res with
    | Some (Module (modName, decls)) ->
        let typesFull = ParserModule.extractTypes false decls
        let typeMap = Map.ofList typesFull
        compileExprOfType typesFull "MessageBody" exprStr
    | _ ->
        failwith "No actor definition found in the file"

// Run FIFT with the construction script, so we have msg_constr.boc ready
// to be executed by tvm_linker
let assembleMsgConstrBoc () =
    FiftExecutor.executeShellCommand "fift" "msg_constr.fif"

let executeMsgConstrBoc tvcPath =
    FiftExecutor.executeShellCommand "tvm_linker" ("test " + tvcPath)

// sourcePath = path to the receiver-actor source code
// destId = a unique identifier of the destination actor
// exprStr = an expression written in Light language that will become
// the message body. For example '{ seqNo = 100; { n = 20 } }' in case
// the contract message type is 'ActorMessage = { n : int }'. SeqNo must increase
// with each new message. The actual seqNo can be inspected by
// getActorState.sh
let generateMsgBoc sourcePath destId exprStr =
    let msgConstrFiftPath = "./msg_constr.fif"
    let msgConstrTvcPath = "./msg_constr.tvc"
    compileMessageBody sourcePath exprStr
    |> (fun expr -> " <{ " + (generateMsgConstructorCode destId expr) + " }>s s>c ")
    |> (fun code -> TVM.genStateInit msgConstrTvcPath code "<b b>")
    |> TVM.dumpFiftScript msgConstrFiftPath
    assembleMsgConstrBoc () |> ignore ;
    executeMsgConstrBoc msgConstrTvcPath |> ignore ;
    extractMsgBoc msgConstrTvcPath

let args = List.ofSeq (System.Environment.GetCommandLineArgs())
if List.length args <> 5 then
    printfn "This script generates message.boc file to be sent into an actor"
    printfn ""
    printfn "USAGE: getActorMessage.fsx <pathToSource> <destId> <expression>"
    exit 1
let sourcePath = args.[2]
let destIdStr = args.[3]
let expr = args.[4]
// let input = Console.ReadLine()
let destId =
    if destIdStr.[0..1] = "0:" then
        "0x" + destIdStr.[2..]
    elif destIdStr.[0..2] = "-1:" then
        failwith "Masterchain messages are not supported"
    else
        failwith "Unknown workchain id in the actor address"

generateMsgBoc sourcePath destId expr
