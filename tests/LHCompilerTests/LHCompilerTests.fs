// For emacs: -*- fsharp -*-

module LHCompilerTests
open NUnit.Framework
open LHExpr
open LHCompiler
open ParserModule

let getLetAst (m:Module) (n:int) =
    m.Decls.[n].letBinding
    |> (function | (_, _, _, c) -> c)

let execAndCheckPrint (prog:string) addInit debug expected =
    if debug then
        printfn "%A" prog |> ignore
        printfn "Passing program to the compiler..."
    let code = LHCompiler.compile prog addInit debug
    if debug then
        printfn "Dumping compiled program into file..."
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename code
    if debug then
        printfn "Executing the resulting FIFT-script..."
    let res = FiftExecutor.runFiftScript filename
    Assert.AreEqual (expected, res)

let execAndCheck prog expected =
    execAndCheckPrint prog false false expected

//let execActorMain prog actorMainParams debug expected =
//    execAndCheckPrintActorMain prog actorMainParams true debug expected

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testBetaRedex0 () =
    let sexpr = SLet ("x", SNum 5, SAdd (SVar "x", SNum 10))
    let res = (betaRedexStep (toAST sexpr)).toSExpr ()
    let expected = SAdd (SNum 5, SNum 10)
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex1 () =
    let sexpr = SLet ("x", SNum 5, SLet ("y", SNum 10, SAdd (SVar "x", SVar "y")))
    let res = (betaRedexStep (toAST sexpr)).toSExpr ()
    let expected = SLet ("y", SNum 10, SAdd (SNum 5, SVar "y"))
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex2 () =
    let sexpr = SLet ("x", SNum 5, SLet ("y", SNum 10, SAdd (SVar "x", SVar "y")))
    let res = (betaRedexStep (betaRedexStep (toAST sexpr))).toSExpr ()
    let expected = SAdd (SNum 5, SNum 10)
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex3 () =
    // let apply = \f.\x.f x in (apply plus1)
      // --> (\f.\x.f x) plus1
    let sexpr = SLet ("apply", SFunc (("f",None), SFunc (("x",None), SAp (SVar "f", SVar "x"))),
                      SAp (SVar "apply", SVar "plus1"))
    let res = (betaRedexStep (toAST sexpr)).toSExpr ()
    let expected = SAp (SFunc (("f",None), SFunc (("x",None), SAp (SVar "f", SVar "x"))), SVar "plus1")
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex4 () =
    // let apply = \f.\x.f x in (apply plus1)
      // --> (\f.\x.f x) plus1
      // --> \x plus1 x
    let sexpr = SLet ("apply", SFunc (("f",None), SFunc (("x",None), SAp (SVar "f", SVar "x"))),
                      SAp (SVar "apply", SVar "plus1"))
    let res = (betaRedexStep (betaRedexStep (toAST sexpr))).toSExpr ()
    let expected = SFunc (("x",None), SAp (SVar "plus1", SVar "x"))
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex5 () =
    // let apply = \f.\x.f x in (apply plus1 5)
      // --> ((\f.\x.f x) plus1) 5
      // --> (\x plus1 x) 5
      // --> plus1 5
    let sexpr = SLet ("apply", SFunc (("f", None), SFunc (("x", None), SAp (SVar "f", SVar "x"))),
                      SAp (SAp (SVar "apply", SVar "plus1"), SNum 5))
    let res = (betaRedexStep (betaRedexStep (betaRedexStep (toAST sexpr)))).toSExpr ()
    let expected = SAp (SVar "plus1", SNum 5)
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex6 () =
    // (\y .(\x . y + 1)) (x + 1) 1
    let sexpr =  SAp (SAp (SFunc (("y", None), SFunc (("x", None), SAdd (SVar "y", SNum 1))),
                           SAdd (SVar "x", SNum 1)),
                      SNum 1)
    let res = (betaRedexStep (toAST sexpr)).toSExpr ()
    let expected = SAp (SFunc (("z0", None), SAdd (SAdd (SVar "x", SNum 1), SNum 1)), SNum 1)
    Assert.AreEqual (expected, res)

[<Test>]
let testBetaRedex7 () =
    // (\x . (\x . x + 1) (x + 1) ) 1
    let sexpr = SAp (SFunc ( ("x", None),
                       SAp (SFunc ( ("x", None), SAdd (SVar "x", SNum 1)),
                            SAdd (SVar "x", SNum 1))),
                     SNum 1)
    let res = (betaRedexStep (toAST sexpr)).toSExpr ()
    let expected = SAp (SFunc (("x", None), SAdd (SVar "x", SNum 1)), SAdd (SNum 1, SNum 1))
    Assert.AreEqual (expected, res)


[<Test>]
[<Ignore("Here Beta Expansion is needed")>]
let testCurry1 () =
    let prog = "contract test
                     let main =
                       let apply func x = (func (x + 1)) in
                       let inc x = x + 1 in
                       let apply_inc = apply inc in
                       (apply_inc 1) ;;"
    execAndCheckPrint prog false false "3"

[<Test>]
let testContractSimple () =
    let prog = "contract Simple
                   type State = { bal:int }
                   let main = 0 ;;"
    execAndCheck prog "0"

[<Test>]
let testRecord0 () =
    let prog = "contract Simple
                   type State = { bal:int }
                   let main =
                     let st = { bal = 100 } in
                     st.bal
                   ;;"
    execAndCheck prog "100"

[<Test>]
let testRecord1 () =
    let prog = "contract Simple
                   type State = { bal:int }
                   let main =
                     let sum x y = x + y in
                     let st = { bal = sum 5 10 } in
                     st.bal
                   ;;"
    execAndCheck prog "15"

[<Test>]
let testRecord2 () =
    let prog = "contract Simple
                   type State = { bal:int }
                   let main =
                     let rec sumN n = if (n > 0) then n + (sumN (n - 1)) else 0 in
                     let st = { bal = sumN 5 } in
                     st.bal
                   ;;"
    execAndCheck prog "15"

[<Test>]
[<Timeout(1000)>]
let testRecord3 () =
    let prog = "contract Simple
                   type State = { bal:int }
                   type Data = { st:State }
                   let main =
                     let rec sumN n = if (n > 0) then n + (sumN (n - 1)) else 0 in
                     let st' = { bal = sumN 5 } in
                     { st = st' }
                   ;;"
    execAndCheckPrint prog false false "[ [ 15 ] ]"

[<Test>]
[<Timeout(1000)>]
let testTuple0 () =
    let prog = "contract Simple
                   let main = ()
                   ;;"
    execAndCheck prog "(null)"

[<Test>]
[<Timeout(1000)>]
let testTuple1 () =
    let prog = "contract Simple
                   let main =
                      let func x y () = x + y in
                      func 5 6 ()
                   ;;"
    execAndCheck prog "11"

[<Test>]
[<Timeout(1000)>]
let testTuple2 () =
    let prog = "contract Simple
                type Rec = { a:int; b:int }
                let main =
                  let func x y () = { a = x; b = y } in
                      func 5 6 ()
                   ;;"
    execAndCheck prog "[ 5 6 ]"

[<Test>]
[<Timeout(1000)>]
let testTuple3 () =
    let prog = "contract Simple
                type ActorState = {
                 seqno: int;
                 deployed: bool
                }
                let main =
                  let actorStateRead () =
                    { seqno = 1; deployed = false } in
                  let actorStateWrite st = () in
                  let act_st = actorStateRead () in
                  if act_st.seqno = 10 then
                      failwith 100
                  else
                      actorStateWrite 1
                  ;;"
    execAndCheckPrint prog false false "(null)"

[<Test>]
[<Timeout(1000)>]
[<Ignore("bug")>]
let testRecord4 () =
    let prog = "contract Simple
                type State = { bal:int }
                type Data = { st:State }
                let main msgCell st = { bal = 1000 } ;;"
    execAndCheckPrint prog true true "[ [ 15 ] ]"

[<Test>]
let testRecord5 () =
    let prog = "contract Simple
                type State = { bal:int }
                let stateDefault = { bal = 0 } ;;
                let func1 (x:State) = x.bal ;;
                let main msgCell (st:State) =
                    { bal = func1 st + 1000 } ;; "
    execAndCheckPrint prog true true "[ 1000 ]"

[<Test>]
[<Timeout(1000)>]
let testLet0() =
    let prog = "contract Simple
                   let other x = x + 1 ;;
                   let main = other 10 ;;"
    execAndCheckPrint prog false false "11"


[<Test>]
let testMkAdder () =
    // TODO!!:
    // In this example, if you change
    // "let adder y = 1 + y" for
    // "let adder y = 1 + x" where x is bound in
    // the make_adder, the result will be incorrect.
    let prog = "contract test
                 let main =
                   let make_adder x =
                     let adder y = 1 + y in
                     adder x
                   in make_adder 3 ;;"
    execAndCheckPrint prog false false "4"

[<Test>]
[<Ignore("bug")>]
let testCurry2 () =
    // This example is interesting. Without beta-reduction,
    // it will not work: function f is general, so in its
    // body there will be Eval node unless we insert its
    // body in main definition. Seems, for such functions,
    // we _must_ do beta-reduction.
    let prog = "contract test
                     let main =
                       let f f1 f2 x y = f2 (f1 x) (f1 y) in
                       let sum x y = x + y in
                       let inc x = x + 1 in
                       f inc sum 10 20 ;;"
    execAndCheckPrint prog false true "32"
