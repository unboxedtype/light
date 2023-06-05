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
[<Timeout(1000)>]
let testTuple0 () =
    let prog = "contract Simple
                   let main = ()
                   ;;"
    execAndCheck prog "(null)"

[<Test>]
let testRecord5 () =
    let prog = "contract Simple
                type State = { bal:int }
                let main =
                  let stateDefault = { bal = 0 } in
                  let func1 (x:State) = x.bal in
                  let main2 func11 stdef =
                    let func2 f x = (f x) + 1000 in
                    { bal = func2 func11 stdef + 1000 } in
                  main2 func1 stateDefault ;;"
    execAndCheckPrint prog false false "[ 2000 ]"

[<Test>]
let testBoolCheck () =
    let prog = "contract test
                let main =
                  let x = 5 in
                  let y = 3 in
                  let z = (x = y) in
                  z ;;"
    execAndCheck prog "0"

[<Test>]
let testNotFalse () =
    let prog = "contract test
                let main = not (false) ;;"

    execAndCheck prog "-1"

[<Test>]
let testNotLt () =
    let prog = "contract test
                let main = not (1 < 3) ;;"

    execAndCheck prog "0"

[<Test>]
let testNotNotLt () =
    let prog = "contract test
                let main = not not 1 < 3 ;;"

    execAndCheck prog "-1"

[<Test>]
let testCmpBool () =
    let prog = "contract test
                let main = true = false ;;"

    execAndCheck prog "0"

[<Test>]
let testCmpBool2 () =
    let prog = "contract test
                let main = true = true ;;"

    execAndCheck prog "-1"

[<Test>]
let testCmpGtEq () =
    let prog1 = "contract test
                let main = 5 >= 5 ;;"
    execAndCheck prog1 "-1"
    let prog2 = "contract test
                let main = 4 >= 5 ;;"
    execAndCheck prog2 "0"
    let prog3 = "contract test
                let main = 6 >= 5 ;;"
    execAndCheck prog3 "-1"

[<Test>]
let testCmpLtEq () =
    let prog1 = "contract test
                let main = 5 <= 5 ;;"
    execAndCheck prog1 "-1"
    let prog2 = "contract test
                let main = 4 <= 5 ;;"
    execAndCheck prog2 "-1"
    let prog3 = "contract test
                let main = 6 <= 5 ;;"
    execAndCheck prog3 "0"

[<Test>]
[<Ignore("str not implemented")>]
let testStr1 () =
    let prog = "contract test
                let main = \"test\" ;;"

    execAndCheck prog "0"



[<Test>]
[<Timeout(1000)>]
let testLet0() =
    let prog = "contract Simple
                   let other x = x + 1 ;;
                   let main = other 10 ;;"
    execAndCheck prog "11"

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
let testMkAdder () =
    let prog = "contract test
                 let main =
                   let make_adder x =
                     let adder y = x + y in
                     adder x
                   in make_adder 3 ;;"
    execAndCheckPrint prog false false "6"

[<Test>]
let testClosure1 () =
    let prog = "contract test
                 let main =
                   let c = 1000 in
                   let make_adder x = x + c in
                     let adder y = make_adder y in
                       adder 3 ;;"
    execAndCheckPrint prog false false "1003"

[<Test>]
let testClosure2 () =
    let prog = "contract test
                let main =
                  let c = 1000 in
                   let make_adder x =
                      (let adder y = y + c in adder x + c)
                   in make_adder 3 ;;"
    execAndCheckPrint prog false false "2003"

[<Test>]
let testClosure3 () =
    let prog = "contract test
                let main =
                  let c = 1000 in
                   let make_adder x =
                      (let adder y = y + c in adder x + c)
                   in make_adder 3 ;;"
    execAndCheckPrint prog false false "2003"


// The tests below contain fixpoint operator. We separate it into a
// different block because it is easier to test separately. Maybe
// it desereves a separate module altogether.

[<Test>]
let testGlobals () =
    let prog = "contract test
                     let main =
                       let mArg = 20 in
                       let nArg = 10 in
                       let rec sum n m =
                           if (n > 0) then (n + ((sum (n - 1)) m)) else m
                       in ((sum nArg) mArg) ;;"
    execAndCheck prog "75"

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
let testGlobals2 () =
    let prog = "contract test
                     let mArg n = n + 20 ;;
                     let nArg n = n + 10 ;;
                     let main =
                       let rec sum n m =
                           if (n > 0) then (n + ((sum (n - 1)) m)) else m
                       in ((sum (nArg 0)) (mArg 0)) ;;"
    execAndCheckPrint prog false false "75"


[<Test>]
let testFunc2Args () =
    // let rec sum n m = if (n > 0) then (n + sum (n - 1) m) else m
    // let sum = fixpoint \sum . \n . \m -> if (...)
    // sum 10 20
    let prog = "contract test
                let main =
                  let rec sum n m =
                       if (n > 0) then (n + ((sum (n - 1)) m)) else m
                  in ((sum 10) 20) ;;"
    execAndCheck prog "75"

[<Test>]
let testFactorialParse () =
    let prog ="contract test
                let main =
                 let rec factorial n =
                      if (n > 1) then (n * factorial (n - 1)) else 1 in
                 factorial 5 ;;
    "
    execAndCheck prog "120"

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
let testInitRecord6 () =
    let prog = "contract Simple
                type State = { bal:int }
                let actorArgs =
                    assembly \"1000 INT 2000 INT NEWC ENDC 2 INT NEWC 32 STU ENDC CTOS TRUE 5 TUPLE\" ;;
                let stateDefault =
                    { bal = 0 } ;;
                let func1 (x:State) =
                    x.bal ;;
                let main msgCell (st:State) =
                    { bal = func1 st + 1000 } ;; "
    execAndCheckPrint prog true false "(null)"   // unit ()


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
    execAndCheckPrint prog false false "32"

[<Test>]
[<Timeout(1000)>]
let testChain1 () =
    let prog = "contract Simple
                let main = () ; (1) ;;"
    execAndCheckPrint prog false false "1"

[<Test>]
[<Timeout(1000)>]
let testChain2 () =
    let prog = "contract Simple
                let someFunc x =
                    x + 1; () ;;
                let main = someFunc 100 ;;"
    execAndCheckPrint prog false false "(null)"

[<Test>]
[<Timeout(1000)>]
let testChain3 () =
    let prog = "contract Simple
                let someFunc x = x + 1; () ;;
                let main = someFunc 100 ;;"
    execAndCheckPrint prog false false "(null)"
