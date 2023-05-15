// For emacs: -*- fsharp -*-

module LHTypeInferTests

open NUnit.Framework
open type LHMachine.Expr
open type LHTypes.Type

[<Test>]
let testENum1 () =
    let ast = ENum 10
    let env = Map []
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);
