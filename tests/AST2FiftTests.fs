module AST2FiftTests

open NUnit.Framework
open System.Diagnostics
open System.Threading.Tasks
open AST2Fift

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let BoolFalseTest () =
    let s = AST2Fift (BoolVal false)
    Assert.AreEqual (["0 INT"], s);

[<Test>]
let BoolTrueTest () =
    let s = AST2Fift (BoolVal true)
    Assert.AreEqual (["-1 INT"], s);

[<Test>]
let NumValTest () =
    let s = AST2Fift (NumVal 1000)
    Assert.AreEqual (["1000 INT"], s);

[<Test>]
let Add2Test () =
    let sum = AST2Fift (Add (NumVal 1000, NumVal 1234))
    Assert.AreEqual (["1000 INT"; "1234 INT"; "ADD"], sum)
