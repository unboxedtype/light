module AST2FiftTests

open NUnit.Framework
open System.Diagnostics
open System.Threading.Tasks

[<OneTimeSetUp>]
let Setup () =
    ()

[<Test>]
let BoolFalseTest () =
    let s = AST2Fift.AST2Fift (AST2Fift.BoolVal false)
    Assert.AreEqual (["0 INT"], s);
