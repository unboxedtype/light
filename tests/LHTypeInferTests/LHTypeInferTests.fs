// For emacs: -*- fsharp -*-

module LHTypeInferTests

open NUnit.Framework
open type LHMachine.Expr
open type LHTypes.Type

[<SetUp>]
let SetupBeforeEachTest () =
    printfn "Executing test: %s" NUnit.Framework.TestContext.CurrentContext.Test.Name

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
let testIf2 () =
    let ast = EFunc ("x", EIf (EVar "x", ENum 10, ENum 20))
    let env = Map []
    Assert.AreEqual(Function (Bool, Int 256), LHTypeInfer.typeInference env ast);

[<Test>]
let testIf3 () =
    let ast = EFunc ("x", EIf (EVar "x", EFunc ("y", EVar "y"), EFunc ("z", EVar "z")))
    let env = Map []
    match (LHTypeInfer.typeInference env ast) with
        | Function (Bool, Function (TVar s1, TVar s2)) when s1 = s2 ->
            Assert.Pass()
        | _ as p ->
            Assert.Fail( sprintf "incorrect type: %A" p )

[<Test>]
let testIf4 () =
    // fun x -> if x then 10 else x
    let ast = EFunc ("x", EIf (EVar "x", ENum 10, EVar "x"))
    let env = Map []
    try
        let res = LHTypeInfer.typeInference env ast
        printfn "%A" res
    with
    | _ ->
        Assert.Pass() ;
    Assert.Fail( "must not typecheck" )

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

[<Test>]
let testRecFunc1 () =
    let ast = ELetRec ("fact",
               EFunc ("n",
                EIf (EGt (EVar "n", ENum 1),
                     EMul (EVar "n",
                       EAp (EVar "fact", ESub (EVar "n", ENum 1))),
                     ENum 1)),
               EVar "fact")
    let env = Map []
    Assert.AreEqual(Function (Int 256, Int 256),
                    LHTypeInfer.typeInference env ast);

[<Test>]
let testRecFunc2 () =
    // tail-recursive factorial
    // let rec fact n res = if (n > 1) then fact (n-1) (n*res) else res
    let ast =
        ELetRec ("fact",
          EFunc ("n",
           EFunc ("res",
            EIf (EGt (EVar "n", ENum 1),
                 EAp (EAp (EVar "fact", ESub (EVar "n", ENum 1)), EMul (EVar "res", EVar "n")),
                 ENum 1))),
          EVar "fact")
    let env = Map []
    Assert.AreEqual(Function (Int 256, Function (Int 256, Int 256)),
                    LHTypeInfer.typeInference env ast);

[<Test>]
let testRecFunc3 () =
    // tail-recursive factorial
    // let rec fact n res = if (n > 1) then fact (n-1) (n*res) else res
    let ast =
        ELetRec ("fact",
          EFunc ("n",
           EFunc ("res",
            EIf (EGt (EVar "n", ENum 1),
                 EAp (EAp (EVar "fact", ESub (EVar "n", ENum 1)), EMul (EVar "res", EVar "n")),
                 ENum 1))),
          EAp (EAp (EVar "fact", ENum 10), ENum 1))
    let env = Map []
    Assert.AreEqual(Int 256,
                    LHTypeInfer.typeInference env ast);

[<Test>]
let testEval1 () =
    // f x = x - 1  : Int -> Int
    // main _ = (f 5) : Int
    let ast = ELet ("f", EFunc ("x", ESub (EVar "x", ENum 1)),
                 ELet ("main", EAp (EVar "f", ENum 5), EVar "main"))
    let env = Map []
    Assert.AreEqual(Int 256,
                    LHTypeInfer.typeInference env ast);
[<Test>]
let testEvalCurry1 () =
    // f = \f1 -> \f2 -> \x -> \y -> f2 (f1 x) (f1 y)
    let f cont =
        ELet ("f",
          EFunc ("f1",
           EFunc ("f2",
            EFunc ("x",
             EFunc ("y", EAp (EAp (EVar "f2", EAp (EVar "f1", EVar "x")),
                                    EAp (EVar "f1", EVar "y")))))), cont)
    // sum = \x -> \y -> x + y
    let sum cont =
        ELet ("sum",
          EFunc ("x",
           EFunc ("y",
            EAdd (EVar "x", EVar "y"))), cont)
    // let inc = \x -> x + 1
    let inc cont =
        ELet ("inc",
          EFunc ("x",
           EAdd (EVar "x", ENum 1)), cont)

    // main = f inc sum 10 20 = sum (inc 10) (inc 20) : Int
    let main = ELet ("main",
                EAp (EAp (EAp (EAp (EVar "f", EVar "inc"), EVar "sum"), ENum 10), ENum 20),
                EVar "main")
    let ast = f (sum (inc main))
    let env = Map []
    Assert.AreEqual(Int 256,
                    LHTypeInfer.typeInference env ast);

[<Test>]
let testLet4 () =
    let ast = ELet ("k", ENum 3, ELet ("t", ENum 4, EVar "t"))))
