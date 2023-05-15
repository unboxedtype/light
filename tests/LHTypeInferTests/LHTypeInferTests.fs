// For emacs: -*- fsharp -*-

module LHTypeInferTests

open NUnit.Framework
open type LHMachine.Expr
open type LHTypes.Type

[<Test>]
let testBasic () =
    let ast0, ast1 = ENum 10, ENull
    let env = Map []
    Assert.AreEqual( (Int 256, Unit), (LHTypeInfer.typeInference env ast0,
                                       LHTypeInfer.typeInference env ast1) );
[<Test>]
let testLet1 () =
    let ast = ELet ("x", ENum 1, EVar "x")
    let env = Map []
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);
