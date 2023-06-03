// For emacs: -*- fsharp -*-

module LHMachineTests

open FSharp.Text.Lexing
open LHMachine
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
    TVM.dumpFiftScript filename (compileIntoFiftDebug expr [] (Map []) ifPrint)
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

let execAndCheck g expected =
    execAndCheckPrint g expected false

[<Test>]
let testTrivial () =
    let code = compile (ASTNode (ASTNode.newId (), ENum 0)) []
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
    let expr = SLet ("main", SFunc (("n",None), SAdd (SVar "n", SNum 1000)), SAp (SVar "main", SNum 2000))
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
                   SAdd (SVar "x", SNum 1000)), SAp (SVar "add", SVar "n"))),
                     SAp (SVar "main", SNum 1000))
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

[<Test>]
let testFactorialParse () =
    let res = parse "contract test
                     let main =
                       let rec factorial n =
                          if (n > 1) then (n * factorial (n - 1)) else 1 in
                       factorial 5 ;;
    "
    let resAst = getLetAst res.Value 0
    execAndCheck resAst "120"

[<Test>]
let testFunc2Args () =
    // let rec sum n m = if (n > 0) then (n + sum (n - 1) m) else m
    // let sum = fixpoint \sum . \n . \m -> if (...)
    // sum 10 20
    let res = parse "contract test
                     let main =
                       let rec sum n m =
                           if (n > 0) then (n + ((sum (n - 1)) m)) else m
                       in ((sum 10) 20) ;;"
    let resAst = getLetAst res.Value 0
    execAndCheck resAst "75"

[<Test>]
let testGlobals () =
    let res = parse "contract test
                     let main =
                       let mArg = 20 in
                       let nArg = 10 in
                       let rec sum n m =
                           if (n > 0) then (n + ((sum (n - 1)) m)) else m
                       in ((sum nArg) mArg) ;;"
    let resAst = getLetAst res.Value 0
    execAndCheckPrint resAst "75" false

[<Test>]
let testCurry0 () =
    let res = parse "contract test
                     let main =
                       let inc x = x + 1 in
                       let apply_inc x = inc x in
                         apply_inc 2 ;;"
    let resAst = getLetAst res.Value 0
    execAndCheckPrint resAst "3" false
