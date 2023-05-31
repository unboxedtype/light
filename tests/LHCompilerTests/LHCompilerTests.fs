// For emacs: -*- fsharp -*-

module LHCompilerTests

open NUnit.Framework

let execAndCheckPrint (prog:string) expected addInit debug =
    if debug then
        printfn "%A" prog |> ignore
    // Here we compile without ActorInit code. This is because
    // we want to capture the exact behavior of the piece.
    if debug then
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
    execAndCheckPrint prog expected false false

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
    execAndCheckPrint prog "[ [ 15 ] ]" false false

[<Test>]
[<Timeout(1000)>]
let testTuple0 () =
    let prog = "contract Simple
                   let main = ()
                   ;;"
    execAndCheckPrint prog "(null)" false false

[<Test>]
[<Timeout(1000)>]
let testTuple1 () =
    let prog = "contract Simple
                   let main =
                      let func x y () = x + y in
                      func 5 6 ()
                   ;;"
    execAndCheckPrint prog "11" false false

[<Test>]
[<Timeout(1000)>]
let testTuple2 () =
    let prog = "contract Simple
                type Rec = { a:int; b:int }
                let main =
                  let func x y () = { a = x; b = y } in
                      func 5 6 ()
                   ;;"
    execAndCheckPrint prog "[ 5 6 ]" false false

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
    execAndCheckPrint prog "(null)" false true

[<Test>]
[<Timeout(1000)>]
[<Ignore("bug")>]
let testRecord4 () =
    let prog = "contract Simple
                   type State = { bal:int }
                   type Data = { st:State }
                   let main msgCell st =
                     let rec sumN n = if (n > 0) then n + (sumN (n - 1)) else 0 in
                     { st = { bal = (sumN 5) } }
                   ;;"
    execAndCheckPrint prog "[ [ 15 ] ]" true true
