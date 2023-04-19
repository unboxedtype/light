// For emacs: -*- fsharp -*-

module LHCompilerTests
open NUnit.Framework

[<SetUp>]
let Setup () =
    ()

[<Test>]
let testContractSimple () =
    let program = "contract Simple

                   type State = {
                       counter: int;
                       sum: int
                   }

                   let sum a b = a + b ;;

                   handler add_more (x: int) =
                         let sum' = sum state.counter x in
                         let counter' = x in
                         state <- { counter = counter' ; sum = sum' }
                    "
    
    let code = LHCompiler.compile program
    let filename = NUnit.Framework.TestContext.CurrentContext.Test.Name + ".fif"
    TVM.dumpFiftScript filename code
    Assert.Pass();
