// For emacs: -*- fsharp -*-

module LHTypesTests

open NUnit.Framework
open FSharp.Text.Lexing
open ParserModule
open Parser
open type LHTypes.Type

let execAndCheck debug dataCell expected program =
    let fiftScript =
        "\"Asm.fif\" include\n" +
        dataCell + "   " +
        "<{ " + program + " }>s 1000000 gasrunvmcode drop .dump cr .dump cr"
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename fiftScript
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

[<SetUp>]
let Setup () =
    ()

(* *******************************************************************
   The algorithm will generate and add to the scope the following:
   let stateReader (c:VMCell) : State
   We want  to test  that it  works correctly for  any shape  of State
   type.
(* ******************************************************************* *) *)

let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

// extract n-th type definition AST in a form of SExpr
let getTypeDefAst (n:int) (m:Module) : Type  =
    m.Decls.[n].typeDef
    |> (function | (_, t) -> t)

[<Test>]
let testStateGet0 () =
    let prog = "contract StateGet
                type State = { x : int }"
    let dataCell = "<b 100 256 u, b>"
    let debug = true
    let expected = "[ 100 ]"
    parse prog
    |> Option.get
    |> getTypeDefAst 0
    |> LHTypes.deserializeValue
    |> execAndCheck debug dataCell expected

(**
[<Test>]
[<Ignore("outdated")>]
let testStateGet1 () =
    let types = [("state",
                   UserType ("State", LHTypes.PT [("x", (LHTypes.UInt 256));
                                                  ("y", LHTypes.Bool);]))]
    let dataCell = "<b 100 256 u, 1 2 u, b>"
    let g = [("state", [], ENum 0);  // this is a stub; will be replaced
             ("main", [], EFunc ("", EIf (ESelect (EVar "state", EVar "y"),
                                          EMul (ESelect (EVar "state", EVar "x"), ENum 2),
                                          ENum 0)))]
    execAndCheck g types dataCell "200"
**)
