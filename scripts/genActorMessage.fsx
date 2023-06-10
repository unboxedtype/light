// #r "nuget: FsLexYacc" ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/FsLexYacc.Runtime.dll"
open FSharp.Text.Lexing ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/LHTypes.dll" ;;
open LHTypes ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/Parser.dll" ;;
open Parser ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/LHExpr.dll" ;;
open LHExpr ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/LHCompiler.dll" ;;
open LHCompiler ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/LHMachine.dll" ;;
open System ;;
open System.IO ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/Parser.dll" ;;
open ParserModule ;;
#r "/home/unboxedtype/src/lighthouse/src/LHCompiler/bin/Debug/net6.0/TVM.dll" ;;

let parse source =
  let lexbuf = LexBuffer<char>.FromString source
  Parser.start Lexer.read lexbuf ;;

let getLetAst (m:Module) (n:int) =
    m.Decls.[n]

let genSerializer sourcePath exprStr =
  let fileContent = File.ReadAllText sourcePath
  let prog = fileContent + ActorInit.actorInitCode
  // printfn "Full program text:\n%A" prog
  let res = LHCompiler.parse prog
  match res with
  | Some (Module (modName, decls)) ->
      let typesFull = ParserModule.extractTypes false decls
      let typeMap = Map.ofList typesFull
      if Map.tryFind "MessageBody" typeMap = None then
          failwithf "type %A not found" "MessageBody"
      let messageType = typeMap.["Message"]
      let messageWriterCode =
          LHTypes.serializeValue typesFull messageType
      let fullTypeDecls = typesFull |> List.map ParserModule.TypeDef
      let res1  = LHCompiler.parse ("contract Test\nlet main = " + exprStr + " ;; ")
      let letBndMain = getLetAst res1.Value 0
      let exprObjectCode =
          LHCompiler.compileModule "test" (fullTypeDecls @ [letBndMain]) false false
      LHMachine.asmAsCell (exprObjectCode + "\n" + messageWriterCode + "\n" + "c4 POP")
      |> (fun c -> TVM.genStateInit "writer.tvc" c "<b b>")
      |>  TVM.dumpFiftScript "writer.fif"
  | _ ->
      failwith "No actor definition found in the file"

let args = List.ofSeq (System.Environment.GetCommandLineArgs())
if List.length args <> 3 then
    printfn "This script generates a message body part of the message boc"
    printfn "USAGE: getActorMessage.fsx <pathToSource>"
let sourcePath = args.[2]
let input = Console.ReadLine()
genSerializer sourcePath input
