// For emacs: -*- fsharp -*-

module LHCompilerTests

open NUnit.Framework


[<SetUp>]
let Setup () =
    ()

[<Test>]
let testContractSimple () =
    let program = "contract Simple
                   type State = { bal:int }
                   let main msg st = 0 ;; " + ActorInit.actorInitCode
    let code = LHCompiler.compile program true
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename code
    Assert.Pass();

[<Test>]
let testGenStateInit0 () =
    // without ACCEPT, the actor will not get deployed
    let code = "<{ ACCEPT 777 INT }>s s>c"
    let data = "<b b>"
    let fift = LHCompiler.generateStateInit "testGenStateInit0.tvc" code data
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename fift
    Assert.Pass();
