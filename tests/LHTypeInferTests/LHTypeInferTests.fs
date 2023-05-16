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

[<Test>]
let testAp1 () =
    let ast = EAp ( EFunc ("x", EVar "x"), ENum 1 )
    let env = Map []
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);

[<Test>]
let testAdd1 () =
    let ast = EAdd (EVar "x", ENum 1)
    let env = Map [("x", LHTypeInfer.Scheme ([],Int 256))]
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);

[<Test>]
let testIf1 () =
    let ast = EIf (EGt (EVar "x", ENum 1), ENum 10, ENum 20)
    let env = Map [("x", LHTypeInfer.Scheme ([],Int 256))]
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);

[<Test>]
let testFunc1 () =
    let ast = EFunc ("x", EAdd (EVar "x", ENum 1))
    let env = Map []
    Assert.AreEqual(Function (Int 256, Int 256), LHTypeInfer.typeInference env ast);

[<Test>]
let testAp2 () =
    let ast = EAp (EFunc ("x", EAdd (EVar "x", ENum 1)), ENum 10)
    let env = Map []
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);

[<Test>]
let testAp3 () =
    let ast = EAp (EFunc ("x", EAdd (EVar "x", ENum 1)), ENum 10)
    let env = Map []
    Assert.AreEqual(Int 256, LHTypeInfer.typeInference env ast);

[<Test>]
let testAp4 () =
    // fun f -> fun n -> f (n + 1)
    let ast = EFunc ("f", EFunc ("n", EAp (EVar "f", EAdd (EVar "n", ENum 1))))
    let env = Map []
    match (LHTypeInfer.typeInference env ast) with
        | Function (Function (Int 256, TVar s1), Function (Int 256, TVar s2)) when s1 = s2 ->
            Assert.Pass()
        | _ as p ->
            Assert.Fail( sprintf "incorrect type: %A" p )
