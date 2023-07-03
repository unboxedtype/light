// For emacs: -*- fsharp -*-

module SDKInteropTests

open SDKInterop
open NUnit.Framework

[<SetUp>]
let Setup () =
    ()

[<Test>]
let test1 () =
    let contractCode =
        "ACCEPT
         PUSHCONT { PUSHINT 1 }
         NEWC
         STCONT
         ENDC
         POP c4"
    let accNew = executeCode client contractCode
    let jsonNull = parseAccount client accNew
    let json = (jsonNull.GetValueOrDefault())
    let dataBocB64 = (json.GetProperty("data"))
    Assert.Pass()

[<Test>]
let test2 () =
    let contractCode =
        "DROP
         PUSHINT 100"
    let res = executeTVMCode client contractCode
    Assert.AreEqual ( "100", res.Value.[0].ToString() )

[<Test>]
let test3 () =
    let contractCode =
        "DROP
         PUSHCONT { PUSHINT 200 }"
    let res = executeTVMCode client contractCode
    Assert.AreEqual ( "Continuation", res.Value.[0].GetProperty("type").ToString() )

[<Test>]
let test4 () =
    let contractCode =
        "DROP NEWC ENDC"
    let res = executeTVMCode client contractCode
    Assert.AreEqual ( "Cell", res.Value.[0].GetProperty("type").ToString() )
    Assert.AreEqual ( EmptyCellB64, res.Value.[0].GetProperty("value").ToString() )
