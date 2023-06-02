// For emacs: -*- fsharp -*-

module LHCompilerTests

open NUnit.Framework

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
    execAndCheck prog "[ [ 15 ] ]"

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
[<Ignore("bug")>]
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
    execAndCheckPrint prog false true "11"
