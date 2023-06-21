// For emacs: -*- fsharp -*-

module SDKInteropTests

open SDKInterop
open NUnit.Framework

[<SetUp>]
let Setup () =
    ()

[<Test>]
let Test1 () =
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
