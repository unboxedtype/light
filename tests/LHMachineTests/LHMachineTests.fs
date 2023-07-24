// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open LHMachine
open NUnit.Framework

open LHExpr
open type LHMachine.Expr

open TestsCommon

[<Test>]
let testTrivial () =
    let code = compileAST (ASTNode (ASTNode.newId (), ENum 0)) [] (Map [])
    Assert.AreEqual( [Integer 0], code );

[<Test>]
let testVal () =
    // let main = 5 in
    // main
    let expr = SLet ("main", SNum 5, SVar "main")
    execASTAndCheck (toAST expr) "5"

[<Test>]
let testAdd () =
    // let main = 5 in
    // main
    let expr = SLet ("main", SAdd (SNum 5, SNum 1000), SVar "main")
    execASTAndCheck (toAST expr) "1005"

[<Test>]
let testLet1 () =
    // let main = \n -> n + 1000 in
    // main 2000
    let expr = SLet ("main", SFunc (("n",None), SAdd (SVar "n", SNum 1000)), (SAp (SVar "main", SNum 2000)))
    execASTAndCheck (toAST expr) "3000"

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
    execASTAndCheck (toAST expr) "2000"

[<Test>]
let testFactorial () =
    // let rec fact = \n -> if n > 1 then n * (fact (n - 1)) else 1
    // in fact 5
    let expr = SLetRec ("fact",
                  SFunc (("n", None),
                    SIf (SGt (SVar "n", SNum 1),
                         SMul (SVar "n", SAp (SVar "fact", SSub (SVar "n", SNum 1))),
                         SNum 1)), SAp (SVar "fact", SNum 5))
    execASTAndCheck (toAST expr) "120"
