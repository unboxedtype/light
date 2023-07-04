// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open LHMachine
open LHCompiler
open ParserModule
open Parser
open NUnit.Framework

open LHExpr
open type LHMachine.Expr

let parse source =
    let lexbuf = LexBuffer<char>.FromString source
    let res = Parser.start Lexer.read lexbuf
    res

let execAndCheckPrint (expr:ASTNode) expected ifPrint =
    if ifPrint then
        printfn "%A" (expr.toSExpr ())
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    LHMachine.compileAST expr [] (Map [])
    |> LHMachine.compileIRIntoAssembly ifPrint true
    |> asmAsRunVM
    |> TVM.dumpFiftScript filename
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

let execAndCheck g expected =
    execAndCheckPrint g expected false

[<Test>]
let testTrivial () =
    let code = compileAST (ASTNode (ASTNode.newId (), ENum 0)) [] (Map [])
    Assert.AreEqual( [Integer 0], code );

[<Test>]
let testVal () =
    // let main = 5 in
    // main
    let expr = SLet ("main", SNum 5, SVar "main")
    execAndCheck (toAST expr) "5"

[<Test>]
let testAdd () =
    // let main = 5 in
    // main
    let expr = SLet ("main", SAdd (SNum 5, SNum 1000), SVar "main")
    execAndCheck (toAST expr) "1005"

[<Test>]
let testLet1 () =
    // let main = \n -> n + 1000 in
    // main 2000
    let expr = SLet ("main", SFunc (("n",None), SAdd (SVar "n", SNum 1000)), (SAp (SVar "main", SNum 2000)))
    execAndCheck (toAST expr) "3000"

[<Test>]
let testLet2 () =
    // let main = \n ->
      // let add = \x -> x + 1000
      // in add n
    // in main 1000
    let expr = SLet ("main",
                SFunc (("n", None),
                 SLet ("add",
                  SFunc (("x", None),
                   SAdd (SVar "x", SNum 1000)), (SAp (SVar "add", SVar "n")))),
                     (SAp (SVar "main", SNum 1000)))
    execAndCheck (toAST expr) "2000"

[<Test>]
let testFactorial () =
    // let rec fact = \n -> if n > 1 then n * (fact (n - 1)) else 1
    // in fact 5
    let expr = SLetRec ("fact",
                  SFunc (("n", None),
                    SIf (SGt (SVar "n", SNum 1),
                         SMul (SVar "n", SAp (SVar "fact", SSub (SVar "n", SNum 1))),
                         SNum 1)), SAp (SVar "fact", SNum 5))
    execAndCheck (toAST expr) "120"
