// For emacs: -*- fsharp -*-

module LHCompilerTests
open NUnit.Framework
open LHExpr
open LHCompiler
open type LHMachine.Instruction
open TestsCommon

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
    execAndCheck prog ""

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
    execAndCheck prog "[\"2000\"]"

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
    execAndCheck prog "[\"5\",\"6\"]"

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
    execAndCheck prog ""

[<Test>]
let testMkAdder () =
    let prog = "contract test
                 let main =
                   let make_adder x =
                     let adder y = x + y in
                     adder x
                   in make_adder 3 ;;"
    execAndCheck prog  "6"

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
let testClosure1 () =
    let prog = "contract test
                 let main =
                   let c = 1000 in
                   let make_adder x = x + c in
                     let adder y = make_adder y in
                       adder 3 ;;"
    execAndCheck prog "1003"

[<Test>]
let testClosure2 () =
    let prog = "contract test
                let main =
                  let c = 1000 in
                   let make_adder x =
                      (let adder y = y + c in adder x + c)
                   in make_adder 3 ;;"
    execAndCheck prog "2003"

[<Test>]
let testClosure3 () =
    let prog = "contract test
                let main =
                  let c = 1000 in
                   let make_adder x =
                      (let adder y = y + c in adder x + c)
                   in make_adder 3 ;;"
    execAndCheck prog "2003"


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
[<Timeout(1000)>]
let testFun1 () =
    let prog = "contract Simple
                let someFunc = fun x y -> x + y ;;
                let main = someFunc 100 200 ;;"
    execAndCheck prog "300"

[<Test>]
[<Timeout(1000)>]
let testFun2 () =
    let prog = "contract Simple
                let someFunc x = fun y -> x + y ;;
                let main = (someFunc 100) 200 ;;"
    execAndCheck prog "300"

[<Test>]
[<Timeout(1000)>]
let testFun3 () =
    let prog = "contract Simple
                let main =
                  let inc (x:int) = x + 1 in
                  let apply f x = f x in
                  apply inc 1 ;;"
    execAndCheck prog "2"

[<Test>]
let testIRtest0 () =
    let prog = [Integer 100; Integer 200; Add]
    execIR prog  "300"

[<Test>]
let testIRtest1 () =
    let prog = [Integer 100; Function [Push 0; Integer 1; Add; Slide 1]; Apply 1; Execute]
    execIR prog  "101"

// This test cracks up the mechanism behind the Fixpoint operator.
[<Test>]
[<Timeout(1000)>]
let testIRtest2 () =
    let prog = [Integer 100;
                Function [Asm [TVM.DumpStk];
                          Integer 1; Sub; Push 0; Integer 0; Equal;
                          IfElse ([Integer 777], [Push 1; Apply 1; Execute ])];
                Fixpoint; // 100 (fix f)
                Apply 1;
                Execute]  // !((fix f) 100)
    execIR prog  "777"


[<Test>]
let testFactorial () =
    let prog ="contract test
                let main =
                 let rec factorial n =
                    if (n > 1) then (n * factorial (n - 1)) else 1 in
                 factorial 5 ;;
    "
    execAndCheck prog "120"

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
    execAndCheck prog "75"

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
    execAndCheck prog "[[\"15\"]]"

[<Test>]
[<Ignore("messageReader needs to be inserted. Not there yet")>]
let testInitRecord6 () =
    let prog = "contract Simple
                type State = { bal:int }
                type ActorMessage = { n:int }
                let accept () = assembly \"ACCEPT\" :> unit ;;
                let stateDefault = { bal = 0 } ;;
                let func1 (x:State) = x.bal ;;
                let main msg (st:State) =
                    accept (); (* accept the message *)
                    { bal = func1 st + 1000 } ;; "

    // This is ActorState structure, not State
    let stateData = "<b 100 256 u, -1 2 i, 777 256 u, b>"
    let debug = false
    execReal debug true prog stateData "(null)"

[<Test>]
let testCurry1 () =
    let prog = "contract test
                     let main =
                       let apply func x = (func (x + 1)) in
                       let inc x = x + 1 in
                       let apply_inc = apply inc in
                       (apply_inc 1) ;;"
    execAndCheck prog "3"

[<Test>]
let testCurry2 () =
    let prog = "contract test
                  let main =
                    let f f1 f2 x y = f2 (f1 x) (f1 y) in
                    let sum x y = x + y in
                    let inc x = x + 1 in
                       f inc sum 10 20 ;;"
    execAndCheck prog "32"

[<Test>]
[<Timeout(1000)>]
let testChain1 () =
    let prog = "contract Simple
                let main = () ; (1) ;;"
    execAndCheck prog "1"

[<Test>]
[<Timeout(1000)>]
let testChain2 () =
    let prog = "contract Simple
                let someFunc x =
                    x + 1; () ;;
                let main = someFunc 100 ;;"
    execAndCheck prog  ""

[<Test>]
[<Timeout(1000)>]
let testChain3 () =
    let prog = "contract Simple
                let someFunc x = x + 1; () ;;
                let main = someFunc 100 ;;"
    execAndCheck prog ""

[<Test>]
let testFib1 () =
    let prog = "contract Fib
                let rec fib n =
                    if n = 0 then 0
                    else if n = 1 then 1
                    else (fib (n - 1) + fib (n - 2)) ;;
                let main = fib 10 ;;"
    execAndCheck prog "55"

[<Test>]
[<Timeout(1000)>]
let testFun4 () =
    let prog = "contract Simple
                let c = 1000 ;;
                let func1 = fun y -> y + c ;;
                let func2 x =
                    fun y -> x + y + (func1 x) ;;
                let main = func2 10 20 ;; (* = 10 + 20 + (10 + 1000)  *)
                "
    execAndCheck prog "1040"

[<Test>]
[<Timeout(1000)>]
let testFun5 () =
    let prog = "contract Simple

                let give x = fun () -> x ;;
                let give1 () = 1000 ;;
                let main = (give give1) () () ;;
                "
    execAndCheck prog "1000"

[<Test>]
[<Timeout(1000)>]
let testFunType () =
    let prog = "contract Simple
                type State = { cont : int -> int }
                let dec n = n - 1 ;;
                let main = { cont = dec }; 0 ;;
                "
    execAndCheck prog "0"

[<Test>]
[<Timeout(1000)>]
let testFunType2 () =
    let prog = "contract Simple
                type State = { cont : int -> int }
                let dec n = n - 1 ;;
                let rec fact n = if (n > 1) then n * fact (n - 1) else 1 ;;
                let main =
                  let st' = { cont = fact } in
                  st'.cont 5
                  ;;
                "
    execAndCheck prog "120"

[<Test>]
[<Timeout(1000)>]
let testFunType3 () =
    let prog = "contract Simple
                type State = { cont : int -> int -> int }
                let sum a b = a + b ;;
                let main =
                  let st' = { cont = sum } in
                  st'.cont 5 10
                  ;;
                "
    execAndCheck prog "15"

[<Test>]
[<Timeout(1000)>]
let testFunType4 () =
    let prog = "contract FunType4
                type ActorState = { cont : VMCell -> State -> VMCell }
                type State = { n : int }
                let cell = assembly { NEWC ; ENDC } :> VMCell ;;
                let step (c:VMCell) (st:State) = cell ;;
                let main =
                    { cont = step }; 0 ;;
                "
    execAndCheck prog "0"

[<Test>]
[<Timeout(1000)>]
[<Ignore ("data format has changed")>]
let testDivergent () =
    let prog = "contract testDivergent
                type State = { b:bool }
                let rec inc_infinite x = 1 + inc_infinite x ;;
                let accept () =
                    assembly \"ACCEPT\" :> unit ;;
                let main =
                    accept () ;
                    inc_infinite 1 ;;
                "
    let debug = false
    execReal debug false prog "<b -1 2 i, b>" "(null)"

[<Test>]
[<Timeout(1000)>]
let testADT1 () =
    let prog = "contract testADT1
                type Vote =
                   | YesVote of int * string
                   | NoVote of int * string
                   | Decision of (int -> int)

                let main =
                    0 ;;
                "
    execAndCheck prog "0"



[<Test>]
[<Ignore("data format has changed")>]
let testRealCont () =
    let prog = "contract testRealCont
                type ActorMessage = { n:int }
                type State = { flip: bool; cont: int -> int; n: int }
                let rec inc x = 1 + x ;;
                let accept () =
                    assembly \"ACCEPT\" :> unit ;;
                let rec fact n = if (n > 1) then n * fact (n - 1) else 1 ;;
                let rec sum n = if (n > 1) then n + sum (n - 1) else 1 ;;
                let main msg (st:State) =
                  accept (); (* accept the message *)
                  let st' =
                    if st.n = 0 then (* workaround for not being able to set conts in stateinit *)
                       { flip = true; cont = inc; n = 2 }
                    else st
                  in
                    if st'.flip then
                        { flip = false; cont = sum; n = st'.cont st'.n }
                    else
                        { flip = true ; cont = inc; n = st'.cont st'.n }
                ;; "
    let stateData = "<b 0 2 i,   // flip
                        B{b5ee9c720101020100160001113fffff0000008040080100109100c8cf43c9ed54} B>boc ref,
                        0 256 u, // n
                      b>"
    let debug = false
    execReal debug false prog stateData "(null)"

[<Test>]
[<Timeout(1000)>]
let testTuple4 () =
    let prog = "contract testADT1
                let main =
                    (0,1,(2,true)) ;;
                "
    execAndCheck prog "[\"0\",\"1\",[\"2\",\"-1\"]]"

[<Test>]
[<Timeout(1000)>]
let testTuple5 () =
    let prog = "contract testTuple5
                let rec fact n = if (n > 1) then n * fact(n - 1) else 1 ;;
                let main =
                    (0,1,2,fact 3) ;;
                "
    execAndCheck prog "[\"0\",\"1\",\"2\",\"6\"]"

[<Test>]
[<Timeout(1000)>]
let testDoubleRec () =
    let prog = "contract testDoubleRec
                type InnerData = { f : (int -> int -> int) }
                type Data = { n : int; func : InnerData }
                type State = { data: Data }
                let main =
                    let st = { data = { n = 10; func = { f = (fun x y -> x + y) } } } in
                    st.data.func.f 5 6  ;;
                "
    execAndCheck prog "11"

[<Test>]
[<Timeout(1000)>]
[<Ignore("not ready yet")>]
let testMatchAdt1 () =
    let prog = "contract testMatchAdt1

                type ActorMessage =
                    | Inc of int
                    | Dec of int

                type State =
                    { n: int }

                (* constructors for ActorMessage type *)
                let Inc (n:int) =
                    assembly \"DUMPSTK ZERO s1 PUSH SINGLE 2 TUPLE NIP \" :> ActorMessage
                ;;
                let Dec (n:int) =
                    assembly \"DUMPSTK ONE  s1 PUSH SINGLE 2 TUPLE NIP \" :> ActorMessage
                ;;

                let proc (msg:ActorMessage) =
                    match msg with
                    | Inc n -> n + 1
                    | Dec n -> n - 1
                ;;

                let main =
                    proc (Inc 10) + proc (Dec 10)
                ;;
              "
    execAndCheck prog "20"

[<Test>]
[<Timeout(1000)>]
let testCastInsideRecord () =
    let prog = "contract testCastInsideRecord
                type State = { data: uint32 }
                let main =
                    { data = 10 :> uint32 } ;;
                "
    execAndCheck prog "[\"10\"]"

[<Test>]
[<Timeout(1000)>]
let testGeLe () =
    let prog1 = "contract testGe
                let main =
                    let f1 x = x + 100 in
                    let f2 y = y * 20 in
                    if (f2 100 >= f1 10) then 10 else 20
                ;;
                "
    execAndCheck prog1 "10"

    let prog2 = "contract testLe
                let main =
                    let f1 x = x + 100 in
                    let f2 y = y * 20 in
                    if (f2 100 <= f1 10) then 10 else 20
                ;;
                "
    execAndCheck prog2  "20"

[<Test>]
[<Timeout(1000)>]
let testIfBool () =
    let prog1 = "contract testIfBoolTrue
                let main =
                    let b = true in
                    if b then 1 else 2
                ;;
                "
    execAndCheck prog1 "1"

    let prog2 = "contract testIfBoolFalse
                let main =
                    let b = false in
                    if b then 1 else 2
                ;;
                "
    execAndCheck prog2  "2"

[<Test>]
[<Timeout(1000)>]
let testTrivialActorInit () =
    let prog = "contract trivialActorInit
                type State = { b : bool }
                type ActorMessage = { b : bool }
                let main msg state =
                    state
                ;;
                "
    let debug = false
    execReal debug true prog "{ seqNo = 0; deployed = false; salt = 0; state = { b = true } }" "(null)"

[<Test>]
let testIRtest5 () =
    let prog = [Integer 100; Integer 200; Add]
    execIR prog  "300"

[<Test>]
[<Timeout(1000)>]
let testIfBool3 () =
    let prog1 = "contract testIfBoolTrue
                let main =
                    let b = true in
                    if b then 1 else 2
                ;;
                "
    execAndCheck prog1 "1" 
